(* Shred the corpus into the seven tables, as COPY text.

   This is the work Phase 1's generated loader will eventually do. It reads the
   same file the row-major path reads, one repository at a time, and derives
   the three things the JSON does not carry: which parent an element belongs to,
   what position it held in its array, and an id for the elements of a scalar
   array, which have none of their own.
   
   Output is COPY text format rather than INSERT statements -- ten million rows
   is not a number of round trips worth making. *)

open Tatami
open Yojson.Safe.Util

let out_dir = ref "corpus/pg"
let corpus = ref "corpus/ci.json"

(* ---- COPY text format ---------------------------------------------------- *)

(* Tab separates, backslash escapes, \N is NULL. Our strings hold quotes but
   the escaping is done properly anyway: a corpus that only happens to be safe
   is a corpus that breaks when the generator changes. *)
type sink = { oc : out_channel; buf : Buffer.t; mutable rows : int }

let sink dir name =
  { oc = open_out_bin (Filename.concat dir (name ^ ".tsv"));
    buf = Buffer.create (1 lsl 20);
    rows = 0 }

let flush_sink s =
  Buffer.output_buffer s.oc s.buf;
  Buffer.clear s.buf

let close_sink s = flush_sink s; close_out s.oc

let esc s v =
  String.iter
    (fun c ->
      match c with
      | '\\' -> Buffer.add_string s.buf "\\\\"
      | '\t' -> Buffer.add_string s.buf "\\t"
      | '\n' -> Buffer.add_string s.buf "\\n"
      | '\r' -> Buffer.add_string s.buf "\\r"
      | c -> Buffer.add_char s.buf c)
    v

let sep s = Buffer.add_char s.buf '\t'
let eol s =
  Buffer.add_char s.buf '\n';
  s.rows <- s.rows + 1;
  if Buffer.length s.buf > (1 lsl 20) then flush_sink s

let wi s v = Buffer.add_string s.buf (string_of_int v)
let wf s v = Buffer.add_string s.buf (Printf.sprintf "%.17g" v)
let wb s v = Buffer.add_string s.buf (if v then "t" else "f")
let wt s v = esc s v
let wnull s = Buffer.add_string s.buf "\\N"
let wot s = function None -> wnull s | Some v -> esc s v
let woi s = function None -> wnull s | Some v -> wi s v

(* ---- reading the JSON ---------------------------------------------------- *)

(* An absent key and an explicit null both arrive here as [`Null], which is the
   right answer: JSON expresses optionality both ways and the schema says only
   that the column is optional. *)
let req k j = match member k j with `Null -> failwith ("missing " ^ k) | v -> v
let gs k j = to_string (req k j)
let gi k j = to_int (req k j)
let gb k j = to_bool (req k j)
let gf k j = match req k j with `Float f -> f | `Int n -> float_of_int n | _ -> failwith k
let os k j = match member k j with `String x -> Some x | _ -> None
let oi k j = match member k j with `Int x -> Some x | _ -> None
let arr k j = match member k j with `List l -> l | _ -> []

(* ---- the shred ----------------------------------------------------------- *)

let () =
  let rec args = function
    | "--corpus" :: v :: r -> corpus := v; args r
    | "--out" :: v :: r -> out_dir := v; args r
    | [] -> ()
    | a :: _ -> prerr_endline ("unknown argument " ^ a); exit 2
  in
  args (List.tl (Array.to_list Sys.argv));
  (try Unix.mkdir !out_dir 0o755 with Unix.Unix_error _ -> ());

  let t_owner = sink !out_dir "owner"
  and t_repo = sink !out_dir "repository"
  and t_topic = sink !out_dir "topic"
  and t_run = sink !out_dir "run"
  and t_job = sink !out_dir "job"
  and t_label = sink !out_dir "label"
  and t_step = sink !out_dir "step" in

  (* Scalar array elements have no id in the JSON, so one is made here. It is
     synthetic and per-table, which is what Phase 1 would do too. *)
  let topic_id = ref 0 and label_id = ref 0 in
  let t0 = Unix.gettimeofday () in

  let n =
    Corpus.iter_json !corpus ~f:(fun repo ->
        let rid = gi "id" repo in

        let ow = req "owner" repo in
        let oid = gi "id" ow in
        wi t_owner oid; sep t_owner; wt t_owner (gs "login" ow); sep t_owner;
        wt t_owner (gs "kind" ow); sep t_owner; wi t_owner (gi "followers" ow);
        sep t_owner; wot t_owner (os "email" ow); eol t_owner;

        wi t_repo rid; sep t_repo; wt t_repo (gs "name" repo); sep t_repo;
        wt t_repo (gs "org" repo); sep t_repo;
        wt t_repo (gs "default_branch" repo); sep t_repo;
        wb t_repo (gb "is_private" repo); sep t_repo;
        wi t_repo (gi "stars" repo); sep t_repo;
        wi t_repo (gi "created_at" repo); sep t_repo;
        wot t_repo (os "description" repo); sep t_repo;
        wi t_repo oid; eol t_repo;

        List.iteri
          (fun i v ->
            incr topic_id;
            wi t_topic !topic_id; sep t_topic; wi t_topic rid; sep t_topic;
            wi t_topic i; sep t_topic; wt t_topic (to_string v); eol t_topic)
          (arr "topics" repo);

        List.iteri
          (fun ri run ->
            let runid = gi "id" run in
            wi t_run runid; sep t_run; wi t_run rid; sep t_run;
            wi t_run ri; sep t_run; wi t_run (gi "number" run); sep t_run;
            wt t_run (gs "commit_sha" run); sep t_run;
            wt t_run (gs "branch" run); sep t_run;
            wt t_run (gs "status" run); sep t_run;
            wi t_run (gi "started_at" run); sep t_run;
            wi t_run (gi "duration_ms" run); sep t_run;
            wot t_run (os "trigger" run); eol t_run;

            List.iteri
              (fun ji job ->
                let jobid = gi "id" job in
                wi t_job jobid; sep t_job; wi t_job runid; sep t_job;
                wi t_job ji; sep t_job; wt t_job (gs "name" job); sep t_job;
                wt t_job (gs "runner_os" job); sep t_job;
                wt t_job (gs "status" job); sep t_job;
                wi t_job (gi "duration_ms" job); sep t_job;
                wi t_job (gi "queued_ms" job); sep t_job;
                woi t_job (oi "exit_code" job); eol t_job;

                List.iteri
                  (fun i v ->
                    incr label_id;
                    wi t_label !label_id; sep t_label; wi t_label jobid;
                    sep t_label; wi t_label i; sep t_label;
                    wt t_label (to_string v); eol t_label)
                  (arr "labels" job);

                List.iteri
                  (fun si st ->
                    wi t_step (gi "id" st); sep t_step; wi t_step jobid;
                    sep t_step; wi t_step si; sep t_step;
                    wt t_step (gs "name" st); sep t_step;
                    wt t_step (gs "status" st); sep t_step;
                    wi t_step (gi "duration_ms" st); sep t_step;
                    wf t_step (gf "cost_per_ms" st); sep t_step;
                    wi t_step (gi "log_bytes" st); sep t_step;
                    wi t_step (gi "memory_mb" st); sep t_step;
                    wot t_step (os "error" st); eol t_step)
                  (arr "steps" job))
              (arr "jobs" run))
          (arr "runs" repo))
  in
  List.iter close_sink [ t_owner; t_repo; t_topic; t_run; t_job; t_label; t_step ];
  let dt = Unix.gettimeofday () -. t0 in
  Printf.eprintf "%d repositories in %.1fs\n" n dt;
  List.iter
    (fun (name, s) -> Printf.eprintf "  %-12s %9d rows\n" name s.rows)
    [ ("owner", t_owner); ("repository", t_repo); ("topic", t_topic);
      ("run", t_run); ("job", t_job); ("label", t_label); ("step", t_step) ];
  Printf.eprintf "%!"
