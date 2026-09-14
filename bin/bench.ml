(* Three stores, the same five questions.

   The answers are compared before any timing is reported. A benchmark between
   stores that return different results is measuring nothing, and the cheapest
   way to be wrong here is to shred a column into the wrong place and never
   notice.

   Each store is loaded, measured, queried and dropped before the next one
   starts, so the footprint figure is that store's and not the sum of whatever
   is still reachable. *)

let now = Unix.gettimeofday
let ms t = t *. 1000.

let median xs =
  let a = Array.of_list xs in
  Array.sort compare a;
  a.(Array.length a / 2)

(* Median of a few, first discarded: the first pays for a cold page cache and
   says more about the machine than about the store. *)
let best ?(n = 5) f =
  ignore (f ());
  let rec go k acc =
    if k = 0 then acc
    else
      let t0 = now () in
      let x = f () in
      go (k - 1) ((now () -. t0, x) :: acc)
  in
  let rs = go n [] in
  (median (List.map fst rs), snd (List.hd rs))

let corpus = ref "corpus/ci.json"
let results_path = ref ""

(* A repo from the middle of the corpus, not the first one. Row-major scans
   until it finds the document, so asking for the first would time one
   comparison rather than a lookup. A repo id is a uuid, so it has to be read
   out of the corpus rather than guessed at. *)
let middle_repo path =
  let ids = ref [] in
  ignore
    (Tatami.Corpus.iter_json path ~f:(fun r ->
         ids := Yojson.Safe.Util.(to_string (member "id" r)) :: !ids));
  let a = Array.of_list (List.rev !ids) in
  a.(Array.length a / 2)
let repeats = ref 5
let threshold = 30_000
let org = "hooli"

type result = {
  store : string;
  load_s : float;
  words : float;
  timings : (string * float) list;
  answers : (string * Tatami.Workload.answer) list;
}

let doc_id = ref ""

let measure (module S : Tatami.Workload.STORE) =
  Gc.full_major ();
  let base = float_of_int (Gc.stat ()).live_words in
  let t0 = now () in
  let s = S.load !corpus in
  let load_s = now () -. t0 in
  Gc.full_major ();
  let words = float_of_int (Gc.stat ()).live_words -. base in
  let queries =
    [ ("document", fun () -> S.document s !doc_id);
      ("scan", fun () -> S.scan s threshold);
      ("computed", fun () -> S.computed s threshold);
      ("by_status", fun () -> S.by_status s);
      ("three_hop", fun () -> S.three_hop s org) ]
  in
  let n = !repeats in
  let runs = List.map (fun (name, f) -> (name, best ~n f)) queries in
  { store = S.name;
    load_s;
    words;
    timings = List.map (fun (n, (t, _)) -> (n, t)) runs;
    answers = List.map (fun (n, (_, a)) -> (n, a)) runs }

let () =
  let rec args = function
    | "--corpus" :: v :: r -> corpus := v; args r
    | "--repeats" :: v :: r -> repeats := int_of_string v; args r
    | "--json" :: v :: r -> results_path := v; args r
    | [] -> ()
    | a :: _ -> prerr_endline ("unknown argument " ^ a); exit 2
  in
  args (List.tl (Array.to_list Sys.argv));

  doc_id := middle_repo !corpus;
  Printf.printf "corpus %s, document %s\n" !corpus !doc_id;

  (* json first: it holds nothing, so it is the cheapest to have resident while
     the others are still being built. *)
  let results =
    [ measure (module Rowmajor.Docs);
      measure (module Rowmajor.Records);
      measure (module Columnar) ]
  in

  (* ---- do they agree ---- *)
  let reference = List.hd results in
  let disagreements = ref 0 in
  List.iter
    (fun r ->
      List.iter2
        (fun (q, a) (_, b) ->
          if not (Tatami.Workload.equal a b) then (
            incr disagreements;
            Printf.printf "  DISAGREE %s on %s: %s vs %s\n" r.store q
              (Tatami.Workload.to_string a) (Tatami.Workload.to_string b)))
        reference.answers r.answers)
    results;
  Printf.printf "\nanswers (%s):\n" reference.store;
  List.iter
    (fun (q, a) -> Printf.printf "  %-10s %s\n" q (Tatami.Workload.to_string a))
    reference.answers;
  if !disagreements > 0 then (
    Printf.printf "\n%d disagreements -- timings below are meaningless\n" !disagreements;
    exit 1);
  print_endline "  all three stores agree";

  (* ---- what each costs to build ---- *)
  Printf.printf "\n%-10s %10s %12s\n" "store" "load" "resident";
  print_endline (String.make 34 '-');
  List.iter
    (fun r ->
      Printf.printf "%-10s %9.2fs %10.0f MB\n" r.store r.load_s
        (r.words *. 8. /. 1e6))
    results;

  (* ---- and to query ---- *)
  Printf.printf "\n%-10s" "query";
  List.iter (fun r -> Printf.printf " %12s" r.store) results;
  Printf.printf " %10s\n" "col vs rec";
  print_endline (String.make 62 '-');
  List.iter
    (fun (q, _) ->
      Printf.printf "%-10s" q;
      let get r = List.assoc q r.timings in
      List.iter (fun r -> Printf.printf " %11.2fms" (ms (get r))) results;
      let rec_t = get (List.nth results 1) and col_t = get (List.nth results 2) in
      Printf.printf " %9.2fx\n" (rec_t /. col_t))
    reference.timings;
  print_newline ();

  (* ---- collected, so the page can chart runs against each other ---- *)
  if !results_path <> "" then begin
    let bytes = (Unix.stat !corpus).st_size in
    let esc s = String.concat "\\\"" (String.split_on_char '"' s) in
    let b = Buffer.create 4096 in
    Buffer.add_string b
      (Printf.sprintf
         "{\"corpus\":\"%s\",\"bytes\":%d,\"repeats\":%d,\"stores\":["
         (esc (Filename.basename !corpus)) bytes !repeats);
    List.iteri
      (fun i r ->
        if i > 0 then Buffer.add_char b ',';
        Buffer.add_string b
          (Printf.sprintf "{\"name\":\"%s\",\"load_ms\":%.2f,\"mb\":%.1f,\"queries\":["
             r.store (ms r.load_s) (r.words *. 8. /. 1e6));
        List.iteri
          (fun k (q, t) ->
            if k > 0 then Buffer.add_char b ',';
            Buffer.add_string b (Printf.sprintf "{\"q\":\"%s\",\"ms\":%.3f}" q (ms t)))
          r.timings;
        Buffer.add_string b "]}")
      results;
    Buffer.add_string b "]}";
    (* one JSON object per line: appending a run never rewrites the earlier ones *)
    let oc = open_out_gen [ Open_append; Open_creat ] 0o644 !results_path in
    output_string oc (Buffer.contents b);
    output_char oc '\n';
    close_out oc;
    Printf.printf "appended to %s\n" !results_path
  end
