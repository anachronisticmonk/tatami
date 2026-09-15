(* Row-major: the documents as OCaml records, deserialised once.

   This is the strong baseline, and it is deliberately good code -- what a
   careful OCaml programmer writes when handed this corpus and no schema
   generator. Nested objects become nested records, arrays become arrays,
   optional fields become [option]. Types are known to the *programmer*, who
   wrote them out by hand; what is missing is not type information but the
   layout that having it machine-generated would license.

   So the difference measured against [Columnar] is layout and nothing else.
   Both know that [ms] is an int and cannot be null. One holds it beside the
   five other fields of the same step; the other holds it beside the [ms] of
   every other step in the corpus. *)

type step = {
  s_id : int;
  s_name : string;
  s_ms : int;
  s_rate : float;
  s_error : string option;
}

type job = {
  j_id : int;
  j_os : string;
  j_status : string;
  j_ms : int;
  j_exit : int option;
  j_steps : step array;
}

type run = {
  r_id : int;
  r_branch : string;
  r_status : string;
  r_ms : int;
  r_trigger : string option;
  r_jobs : job array;
}

type repo = {
  p_id : string;
  p_name : string;
  p_org : string;
  p_private : bool;
  p_runs : run array;
}

(* ---- reading ------------------------------------------------------------- *)

open Yojson.Safe.Util

let gi k j = to_int (member k j)
let gs k j = to_string (member k j)
let gb k j = to_bool (member k j)
let gf k j = match member k j with `Float f -> f | `Int n -> float_of_int n | _ -> 0.

(* Absent and explicitly null are the same thing here, which is what the schema
   says and what the database does. *)
let os k j = match member k j with `String x -> Some x | _ -> None
let oi k j = match member k j with `Int x -> Some x | _ -> None

let arr k j f =
  match member k j with `List l -> Array.of_list (List.map f l) | _ -> [||]

let step j =
  { s_id = gi "id" j; s_name = gs "name" j; s_ms = gi "ms" j;
    s_rate = gf "rate" j; s_error = os "error" j }

let job j =
  { j_id = gi "id" j; j_os = gs "os" j; j_status = gs "status" j;
    j_ms = gi "ms" j; j_exit = oi "exit" j; j_steps = arr "steps" j step }

let run j =
  { r_id = gi "id" j; r_branch = gs "branch" j; r_status = gs "status" j;
    r_ms = gi "ms" j; r_trigger = os "trigger" j; r_jobs = arr "jobs" j job }

let repo j =
  { p_id = gs "id" j; p_name = gs "name" j; p_org = gs "org" j;
    p_private = gb "private" j; p_runs = arr "runs" j run }

(* ---- the store ----------------------------------------------------------- *)

let name = "records"

(* The array of documents, and one lookup beside it: a repo id to its position.
   Neither layout gets that for free -- an id is a uuid, not a row number -- so
   the columnar store builds the same thing and neither side is being handed an
   index the other lacks. *)
type t = { repos : repo array; at : (string, int) Hashtbl.t }

let load path =
  let acc = ref [] in
  ignore (Tatami.Corpus.iter_json path ~f:(fun j -> acc := repo j :: !acc));
  let repos = Array.of_list (List.rev !acc) in
  let at = Hashtbl.create (2 * Array.length repos) in
  Array.iteri (fun i (p : repo) -> Hashtbl.replace at p.p_id i) repos;
  { repos; at }

let footprint (t : t) =
  ignore t;
  Gc.full_major ();
  float_of_int (Gc.stat ()).live_words

(* Every traversal is the same shape -- four nested loops -- because reaching a
   step means walking the documents that contain it. There is no other way in:
   a step is not addressable except through its job, its run, its repo. *)
let iter_steps (t : t) f =
  Array.iter
    (fun p ->
      Array.iter (fun r -> Array.iter (fun j -> Array.iter f j.j_steps) r.r_jobs)
        p.p_runs)
    t.repos

(* One repo, entire. The subtree is already here and already contiguous, so
   this is a walk of the thing itself rather than a search for its parts. *)
let document (t : t) id =
  match Hashtbl.find_opt t.at id with
  | None -> Tatami.Workload.Missing
  | Some i ->
      let p = t.repos.(i) in
      let runs = ref 0 and jobs = ref 0 and steps = ref 0 and ms = ref 0 in
      Array.iter
        (fun r ->
          incr runs;
          Array.iter
            (fun j ->
              incr jobs;
              Array.iter (fun s -> incr steps; ms := !ms + s.s_ms) j.j_steps)
            r.r_jobs)
        p.p_runs;
      Tatami.Workload.Row (List.map string_of_int [ !runs; !jobs; !steps; !ms ])

let scan (t : t) ms =
  let n = ref 0 in
  iter_steps t (fun s -> if s.s_ms > ms then incr n);
  Tatami.Workload.Count !n

let computed (t : t) ms =
  let acc = ref 0. in
  iter_steps t (fun s ->
      if s.s_ms > ms then acc := !acc +. (float_of_int s.s_ms *. s.s_rate));
  Tatami.Workload.Sum_float !acc

(* Grouped by the step's name rather than a status it does not have: which
   command is the slowest one anybody runs. *)
let by_status (t : t) =
  let tbl = Hashtbl.create 8 in
  iter_steps t (fun s ->
      let cur = try Hashtbl.find tbl s.s_name with Not_found -> 0 in
      if s.s_ms > cur then Hashtbl.replace tbl s.s_name s.s_ms);
  Tatami.Workload.Groups
    (List.sort compare (Hashtbl.fold (fun k v a -> (k, v) :: a) tbl []))

(* The three hops are free here, and that is the interesting part: a step is
   already inside the repo that owns it, so there is no join to do. The
   columnar side has to pay for this one. *)
let three_hop (t : t) org =
  let total = ref 0 in
  Array.iter
    (fun p ->
      if String.equal p.p_org org then
        Array.iter
          (fun r ->
            Array.iter (fun j -> Array.iter (fun s -> total := !total + s.s_ms) j.j_steps)
              r.r_jobs)
          p.p_runs)
    t.repos;
  Tatami.Workload.Sum_int !total
