(* Row-major, materialising nothing: the documents on disk, parsed per query.

   The other end of the range from [Columnar]. [Records] pays once to build a
   typed structure; this pays every time and keeps nothing, which is what you
   get if you reach for Yojson and answer the question in front of you.

   It is not a straw man. For one query it is the fastest of the three, because
   the other two are still deserialising when this one has finished. What it
   cannot do is get cheaper on the second question. *)

open Yojson.Safe.Util

let name = "json"

(* The store is the path. Nothing is held. *)
type t = string

let load path = path
let footprint _ = 0.

let gi k j = to_int (member k j)
let gs k j = to_string (member k j)
let gf k j = match member k j with `Float f -> f | `Int n -> float_of_int n | _ -> 0.
let arr k j = match member k j with `List l -> l | _ -> []

(* Every query re-reads and re-parses the file. The four nested loops are the
   same ones [Records] walks -- the difference is that these documents did not
   exist a moment ago and will not exist a moment later. *)
let iter_steps path f =
  ignore
    (Tatami.Corpus.iter_json path ~f:(fun repo ->
         List.iter
           (fun run ->
             List.iter
               (fun job -> List.iter f (arr "steps" job))
               (arr "jobs" run))
           (arr "runs" repo)))

let document path id =
  let found = ref Tatami.Workload.Missing in
  ignore
    (Tatami.Corpus.iter_json path ~f:(fun repo ->
         if !found = Tatami.Workload.Missing && gi "id" repo = id then (
           let runs = ref 0 and jobs = ref 0 and steps = ref 0 and ms = ref 0 in
           List.iter
             (fun run ->
               incr runs;
               List.iter
                 (fun job ->
                   incr jobs;
                   List.iter
                     (fun s -> incr steps; ms := !ms + gi "ms" s)
                     (arr "steps" job))
                 (arr "jobs" run))
             (arr "runs" repo);
           found :=
             Tatami.Workload.Row
               (List.map string_of_int [ !runs; !jobs; !steps; !ms ]))));
  !found

let scan path ms =
  let n = ref 0 in
  iter_steps path (fun s -> if gi "ms" s > ms then incr n);
  Tatami.Workload.Count !n

let computed path ms =
  let acc = ref 0. in
  iter_steps path (fun s ->
      let d = gi "ms" s in
      if d > ms then acc := !acc +. (float_of_int d *. gf "rate" s));
  Tatami.Workload.Sum_float !acc

let by_status path =
  let tbl = Hashtbl.create 8 in
  iter_steps path (fun s ->
      let k = gs "name" s and d = gi "ms" s in
      let cur = try Hashtbl.find tbl k with Not_found -> 0 in
      if d > cur then Hashtbl.replace tbl k d);
  Tatami.Workload.Groups
    (List.sort compare (Hashtbl.fold (fun k v a -> (k, v) :: a) tbl []))

let three_hop path org =
  let total = ref 0 in
  ignore
    (Tatami.Corpus.iter_json path ~f:(fun repo ->
         if String.equal (gs "org" repo) org then
           List.iter
             (fun run ->
               List.iter
                 (fun job ->
                   List.iter
                     (fun s -> total := !total + gi "ms" s)
                     (arr "steps" job))
                 (arr "jobs" run))
             (arr "runs" repo)));
  Tatami.Workload.Sum_int !total
