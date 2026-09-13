(* Row-major: the documents as OCaml records, deserialised once.

   This is the strong baseline, and it is deliberately good code -- what a
   careful OCaml programmer writes when handed this corpus and no schema
   generator. Nested objects become nested records, arrays become arrays,
   optional fields become [option]. Types are known to the *programmer*, who
   wrote them out by hand; what is missing is not type information but the
   layout that having it machine-generated would license.

   So the difference measured against [Columnar] is layout and nothing else.
   Both know that duration_ms is an int and cannot be null. One holds it beside
   nine other fields of the same step; the other holds it beside the duration
   of every other step in the corpus. *)

type step = {
  s_id : int;
  s_name : string;
  s_status : string;
  s_duration_ms : int;
  s_cost_per_ms : float;
  s_log_bytes : int;
  s_memory_mb : int;
  s_error : string option;
}

type job = {
  j_id : int;
  j_name : string;
  j_runner_os : string;
  j_status : string;
  j_duration_ms : int;
  j_queued_ms : int;
  j_exit_code : int option;
  j_labels : string array;
  j_steps : step array;
}

type run = {
  r_id : int;
  r_number : int;
  r_commit_sha : string;
  r_branch : string;
  r_status : string;
  r_started_at : int;
  r_duration_ms : int;
  r_trigger : string option;
  r_jobs : job array;
}

type owner = {
  o_id : int;
  o_login : string;
  o_kind : string;
  o_followers : int;
  o_email : string option;
}

type repository = {
  p_id : int;
  p_name : string;
  p_org : string;
  p_default_branch : string;
  p_is_private : bool;
  p_stars : int;
  p_created_at : int;
  p_description : string option;
  p_owner : owner;
  p_topics : string array;
  p_runs : run array;
}

(* ---- reading ------------------------------------------------------------- *)

open Yojson.Safe.Util

let gi k j = to_int (member k j)
let gs k j = to_string (member k j)
let gb k j = to_bool (member k j)
let gf k j = match member k j with `Float f -> f | `Int n -> float_of_int n | _ -> 0.

(* Absent and explicitly null are the same thing here, which is what the
   schema says and what the database does. *)
let os k j = match member k j with `String x -> Some x | _ -> None
let oi k j = match member k j with `Int x -> Some x | _ -> None

let arr k j f =
  match member k j with
  | `List l -> Array.of_list (List.map f l)
  | _ -> [||]

let step j =
  { s_id = gi "id" j; s_name = gs "name" j; s_status = gs "status" j;
    s_duration_ms = gi "duration_ms" j; s_cost_per_ms = gf "cost_per_ms" j;
    s_log_bytes = gi "log_bytes" j; s_memory_mb = gi "memory_mb" j;
    s_error = os "error" j }

let job j =
  { j_id = gi "id" j; j_name = gs "name" j; j_runner_os = gs "runner_os" j;
    j_status = gs "status" j; j_duration_ms = gi "duration_ms" j;
    j_queued_ms = gi "queued_ms" j; j_exit_code = oi "exit_code" j;
    j_labels = arr "labels" j to_string; j_steps = arr "steps" j step }

let run j =
  { r_id = gi "id" j; r_number = gi "number" j; r_commit_sha = gs "commit_sha" j;
    r_branch = gs "branch" j; r_status = gs "status" j;
    r_started_at = gi "started_at" j; r_duration_ms = gi "duration_ms" j;
    r_trigger = os "trigger" j; r_jobs = arr "jobs" j job }

let owner j =
  { o_id = gi "id" j; o_login = gs "login" j; o_kind = gs "kind" j;
    o_followers = gi "followers" j; o_email = os "email" j }

let repository j =
  { p_id = gi "id" j; p_name = gs "name" j; p_org = gs "org" j;
    p_default_branch = gs "default_branch" j; p_is_private = gb "is_private" j;
    p_stars = gi "stars" j; p_created_at = gi "created_at" j;
    p_description = os "description" j; p_owner = owner (member "owner" j);
    p_topics = arr "topics" j to_string; p_runs = arr "runs" j run }

(* ---- the store ----------------------------------------------------------- *)

let name = "records"

type t = repository array

let load path =
  let acc = ref [] in
  ignore (Tatami.Corpus.iter_json path ~f:(fun j -> acc := repository j :: !acc));
  Array.of_list (List.rev !acc)

(* Live words, measured rather than estimated: the whole point of the
   comparison is that one of these representations is larger than the other. *)
let footprint (t : t) =
  ignore t;
  Gc.full_major ();
  float_of_int (Gc.stat ()).live_words

(* Every traversal is the same shape -- four nested loops -- because reaching a
   step means walking the documents that contain it. There is no other way in:
   a step is not addressable except through its job, its run, its repository. *)
let iter_steps (t : t) f =
  Array.iter
    (fun p ->
      Array.iter
        (fun r -> Array.iter (fun j -> Array.iter f j.j_steps) r.r_jobs)
        p.p_runs)
    t

(* One repository, entire. The subtree is already here and already contiguous,
   so this is a walk of the thing itself rather than a search for its parts. *)
let document (t : t) id =
  let found = ref Tatami.Workload.Missing in
  (try
     Array.iter
       (fun p ->
         if p.p_id = id then (
           let runs = ref 0 and jobs = ref 0 and steps = ref 0 and ms = ref 0 in
           Array.iter
             (fun r ->
               incr runs;
               Array.iter
                 (fun j ->
                   incr jobs;
                   Array.iter
                     (fun s -> incr steps; ms := !ms + s.s_duration_ms)
                     j.j_steps)
                 r.r_jobs)
             p.p_runs;
           found :=
             Tatami.Workload.Row
               (List.map string_of_int [ !runs; !jobs; !steps; !ms ]);
           raise Exit))
       t
   with Exit -> ());
  !found

let scan (t : t) ms =
  let n = ref 0 in
  iter_steps t (fun s -> if s.s_duration_ms > ms then incr n);
  Tatami.Workload.Count !n

let computed (t : t) ms =
  let acc = ref 0. in
  iter_steps t (fun s ->
      if s.s_duration_ms > ms then
        acc := !acc +. (float_of_int s.s_duration_ms *. s.s_cost_per_ms));
  Tatami.Workload.Sum_float !acc

let by_status (t : t) =
  let tbl = Hashtbl.create 8 in
  iter_steps t (fun s ->
      let cur = try Hashtbl.find tbl s.s_status with Not_found -> 0 in
      if s.s_duration_ms > cur then Hashtbl.replace tbl s.s_status s.s_duration_ms);
  Tatami.Workload.Groups
    (List.sort compare (Hashtbl.fold (fun k v a -> (k, v) :: a) tbl []))

(* The three hops are free here, and that is the interesting part: a step is
   already inside the repository that owns it, so there is no join to do. The
   columnar side has to pay for this one. *)
let three_hop (t : t) org =
  let total = ref 0 in
  Array.iter
    (fun p ->
      if String.equal p.p_org org then
        Array.iter
          (fun r ->
            Array.iter
              (fun j -> Array.iter (fun s -> total := !total + s.s_duration_ms) j.j_steps)
              r.r_jobs)
          p.p_runs)
    t;
  Tatami.Workload.Sum_int !total
