(* The demonstration, on localhost:8000. Three tabs:

     data          one document, and the four tables it shreds into
     query         the small corpus, answered by both stores at once
     performance   what has been measured, charted

   The small corpus is loaded into *both* stores when the server starts and
   held there. That is deliberate rather than incidental: a store that is
   rebuilt per request never amortises anything, so a demonstration that
   re-fetched would show the typed arrays at their worst and call it their
   nature. *)

open Tatami
module S = Tiny_httpd

let port = match Sys.getenv_opt "TATAMI_PORT" with Some p -> int_of_string p | None -> 8000

(* Loopback by default, because a development server should not appear on the
   network because someone started it. In a container it has to be 0.0.0.0:
   published ports forward to the container's external interface, so a server
   bound to 127.0.0.1 is reachable only from inside the container it is in --
   which looks exactly like a working server and a broken port mapping. *)
let addr = match Sys.getenv_opt "TATAMI_ADDR" with Some a -> a | None -> "127.0.0.1"
let corpus = ref "corpus/small.json"
let web_dir = match Sys.getenv_opt "TATAMI_WEB" with Some p -> p | None -> "web"
let results = ref "bench/results.jsonl"

let read_file path =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let json ?(code = 200) j =
  S.Response.make_string
    ~headers:[ ("Content-Type", "application/json") ]
    ~code (Ok (Yojson.Safe.to_string j))

let fail code msg = json ~code (`Assoc [ ("error", `String msg) ])

let page path =
  S.Response.make_string
    ~headers:[ ("Content-Type", "text/html; charset=utf-8") ]
    (Ok (read_file (Filename.concat web_dir path)))

(* ---- the schema, as the .mli says it and as we read it ------------------- *)

let column_json (c : Schema.column) =
  `Assoc
    [ ("name", `String c.name);
      ("layout", `String (Schema.layout_to_string c.layout));
      ( "nullable",
        `Bool (match c.layout with Schema.Nullable _ -> true | Schema.Plain _ -> false) );
      ("refers_to", match c.refers_to with None -> `Null | Some t -> `String t) ]

let schema_json () =
  let db = Schema.load_dir "schema" in
  `List
    (List.map
       (fun (t : Schema.t) ->
         `Assoc
           [ ("table", `String t.table);
             ("source", `String (read_file (Filename.concat "schema" (t.table ^ ".mli"))));
             ("columns", `List (List.map column_json t.columns)) ])
       db)

(* ---- one document, and what it becomes ----------------------------------- *)

(* The first repo in the corpus, verbatim, beside the rows it shreds into. The
   two halves are the whole story of the project in one screen: the same data
   as a tree, and as four tables. *)
let sample () =
  let doc = ref `Null in
  (try
     ignore
       (Corpus.iter_json !corpus ~f:(fun j ->
            if !doc = `Null then (doc := j; raise Exit)))
   with Exit -> ());
  let j = !doc in
  let m k v = Yojson.Safe.Util.member k v in
  let arr k v = match m k v with `List l -> l | _ -> [] in
  let s k v = Yojson.Safe.Util.to_string (m k v) in
  let i k v = Yojson.Safe.Util.to_int (m k v) in
  let opt k v = match m k v with `Null -> `Null | x -> x in
  let rid = s "id" j in
  let runs = ref [] and jobs = ref [] and steps = ref [] in
  List.iteri
    (fun ri u ->
      let uid = i "id" u in
      runs :=
        `Assoc
          [ ("id", `Int uid); ("repo_id", `String rid); ("idx", `Int ri);
            ("branch", m "branch" u); ("status", m "status" u); ("ms", m "ms" u);
            ("trigger", opt "trigger" u) ]
        :: !runs;
      List.iteri
        (fun ji jb ->
          let jid = i "id" jb in
          jobs :=
            `Assoc
              [ ("id", `Int jid); ("run_id", `Int uid); ("idx", `Int ji);
                ("os", m "os" jb); ("status", m "status" jb); ("ms", m "ms" jb);
                ("exit", opt "exit" jb) ]
            :: !jobs;
          List.iteri
            (fun si st ->
              steps :=
                `Assoc
                  [ ("id", m "id" st); ("job_id", `Int jid); ("idx", `Int si);
                    ("name", m "name" st); ("ms", m "ms" st); ("rate", m "rate" st);
                    ("error", opt "error" st) ]
                :: !steps)
            (arr "steps" jb))
        (arr "jobs" u))
    (arr "runs" j);
  `Assoc
    [ ("document", j);
      ("repo",
       `List [ `Assoc [ ("id", `String rid); ("name", m "name" j); ("org", m "org" j);
                        ("private_", m "private" j) ] ]);
      ("run", `List (List.rev !runs));
      ("job", `List (List.rev !jobs));
      ("step", `List (List.rev !steps)) ]

(* ---- both stores, resident ----------------------------------------------- *)

let rec_store = ref None
let col_store = ref None
let doc_id = ref ""
let stats = ref (`Assoc [])

let boot () =
  Printf.printf "loading %s\n%!" !corpus;
  let t0 = Unix.gettimeofday () in
  let r = Rowmajor.Records.load !corpus in
  let t1 = Unix.gettimeofday () in
  let c = Columnar.load !corpus in
  let t2 = Unix.gettimeofday () in
  rec_store := Some r;
  col_store := Some c;
  let ids = ref [] in
  ignore (Corpus.iter_json !corpus ~f:(fun j ->
      ids := Yojson.Safe.Util.(to_string (member "id" j)) :: !ids));
  let a = Array.of_list (List.rev !ids) in
  doc_id := a.(Array.length a / 2);
  stats :=
    `Assoc
      [ ("corpus", `String (Filename.basename !corpus));
        ("bytes", `Int (Unix.stat !corpus).st_size);
        ("repos", `Int (Array.length a));
        ("records_load_ms", `Float ((t1 -. t0) *. 1000.));
        ("columnar_load_ms", `Float ((t2 -. t1) *. 1000.));
        ("rows", `Assoc (List.map (fun (n, k) -> (n, `Int k)) (Columnar.(c.rows)))) ];
  Printf.printf "  records %.0fms, columnar %.0fms\n%!" ((t1 -. t0) *. 1000.)
    ((t2 -. t1) *. 1000.)

(* ---- running a query ----------------------------------------------------- *)

(* Five shapes rather than a query language. What is being demonstrated is that
   the same question costs different amounts in the two layouts, and a parser
   would sit between the reader and that without adding to it. *)
let answer_json a = `String (Workload.to_string a)

(* Warmed, then the median of a few.

   A single cold run is not a measurement: the first pass over a store touches
   memory nothing has touched yet, and whichever store goes first pays for it.
   Timed that way the page reported a thirty-six fold win on a query the
   benchmark puts at three, which would have been a lie told by the interface
   rather than by anybody. *)
(* Median of a few, and each sample a batch rather than a single call.

   [document] answers in a fraction of a microsecond -- a hash lookup and one
   repo's subtree -- where gettimeofday resolves about one. Timing it once
   reports the clock: the figure comes back as an exact power of two, which is
   quantisation and not a measurement. So a sample repeats the call until at
   least [floor_s] has passed and divides back down, which is bin/bench.ml's
   rule; it has to be the same rule, or the page and the collected results
   would disagree about the same question.

   The floor is lower here than in the benchmark. This one runs while someone
   waits for it, and 20ms per sample is already twenty thousand times what the
   clock can resolve. *)
let floor_s = 0.02
let max_reps = 1 lsl 22

let batch f k =
  let t0 = Unix.gettimeofday () in
  for _ = 1 to k do ignore (f ()) done;
  Unix.gettimeofday () -. t0

let time ?(n = 5) f =
  let rec calibrate k =
    if k >= max_reps || batch f k >= floor_s then k else calibrate (k * 4)
  in
  let k = calibrate 1 in
  let per () = batch f k /. float_of_int k *. 1000. in
  let rec go i acc = if i = 0 then acc else go (i - 1) (per () :: acc) in
  let sorted = List.sort compare (go n []) in
  (f (), List.nth sorted (n / 2))

(* [type a] ties the module's abstract [t] to the store value handed in;
   without it S.t escapes its scope and the two cannot be related. *)
let pick (type a) (module S : Workload.STORE with type t = a) (s : a) name param :
    unit -> Workload.answer =
  match name with
  | "document" -> fun () -> S.document s param
  | "scan" -> fun () -> S.scan s (int_of_string param)
  | "computed" -> fun () -> S.computed s (int_of_string param)
  | "by_status" -> fun () -> S.by_status s
  | "three_hop" -> fun () -> S.three_hop s param
  | _ -> failwith ("no query " ^ name)

let run_query name param =
  match (!rec_store, !col_store) with
  | Some r, Some c ->
      let param = if name = "document" && param = "" then !doc_id else param in
      (* both warmed before either is timed, so neither pays for the other *)
      let ra, rt = time (pick (module Rowmajor.Records) r name param) in
      let ca, ct = time (pick (module Columnar) c name param) in
      json
        (`Assoc
          [ ("query", `String name); ("param", `String param);
            ("agree", `Bool (Workload.equal ra ca));
            ("records", `Assoc [ ("ms", `Float rt); ("answer", answer_json ra) ]);
            ("columnar", `Assoc [ ("ms", `Float ct); ("answer", answer_json ca) ]);
            ("ratio", `Float (rt /. ct));
            ("samples", `Int 5) ])
  | _ -> fail 503 "stores not loaded"

(* ---- collected measurements ---------------------------------------------- *)

(* One JSON object per line, appended by bin/bench.exe. Served as an array. *)
let bench_json () =
  try
    `List
      (read_file !results |> String.split_on_char '\n'
      |> List.filter (fun l -> String.trim l <> "")
      |> List.map Yojson.Safe.from_string)
  with Sys_error _ -> `List []

(* ---- routes -------------------------------------------------------------- *)

let () =
  let rec args = function
    | "--corpus" :: v :: r -> corpus := v; args r
    | "--results" :: v :: r -> results := v; args r
    | [] -> ()
    | a :: _ -> prerr_endline ("unknown argument " ^ a); exit 2
  in
  args (List.tl (Array.to_list Sys.argv));
  boot ();
  let server = S.create ~addr ~port () in
  let get p h = S.add_route_handler ~meth:`GET server p h in
  let post p h = S.add_route_handler ~meth:`POST server p h in

  get S.Route.return (fun _ -> page "index.html");
  (* one repo, reassembled from the four tables it shredded into *)
  get S.Route.(exact "reassemble" @/ return) (fun _ -> page "reassemble.html");
  get S.Route.(exact "api" @/ exact "schema" @/ return) (fun _ -> json (schema_json ()));
  get S.Route.(exact "api" @/ exact "sample" @/ return) (fun _ ->
      try json (sample ()) with e -> fail 500 (Printexc.to_string e));
  get S.Route.(exact "api" @/ exact "stats" @/ return) (fun _ -> json !stats);
  get S.Route.(exact "api" @/ exact "bench" @/ return) (fun _ -> json (bench_json ()));
  post S.Route.(exact "api" @/ exact "query" @/ return) (fun req ->
      let body = String.trim (S.Request.body req) in
      let name, param =
        match String.index_opt body ' ' with
        | Some i -> (String.sub body 0 i, String.sub body (i + 1) (String.length body - i - 1))
        | None -> (body, "")
      in
      try run_query name param with
      | Failure m -> fail 400 m
      | e -> fail 500 (Printexc.to_string e));

  Printf.printf "tatami: listening on %s:%d\n%!" addr port;
  S.run_exn server
