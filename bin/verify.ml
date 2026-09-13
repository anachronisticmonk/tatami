(* Is the database the same data as the JSON?

   The whole comparison rests on it. If the two stores hold different rows then
   any difference in what they answer is a sampling artefact, and every number
   downstream is worthless. So the same aggregates are computed twice -- once by
   streaming the corpus, once in SQL -- and compared.

   Counts alone would not catch a column shredded into the wrong place, so the
   sums are over specific columns at every level of the nesting, and one of
   them is the product [duration_ms * cost_per_ms] that the workload will
   compute: if the float survived the round trip through COPY text, it survives
   here first. *)

open Tatami
open Yojson.Safe.Util

let corpus = ref "corpus/ci.json"

type tally = {
  mutable repos : int;
  mutable owners : int;
  mutable topics : int;
  mutable runs : int;
  mutable jobs : int;
  mutable labels : int;
  mutable steps : int;
  mutable private_repos : int;
  mutable stars : int;
  mutable queued : int;
  mutable step_ms : int;
  mutable log_bytes : int;
  mutable errors : int;
  mutable exit_codes : int;
  mutable cost : float;
}

let zero () =
  { repos = 0; owners = 0; topics = 0; runs = 0; jobs = 0; labels = 0; steps = 0;
    private_repos = 0; stars = 0; queued = 0; step_ms = 0; log_bytes = 0;
    errors = 0; exit_codes = 0; cost = 0. }

let arr k j = match member k j with `List l -> l | _ -> []
let gi k j = to_int (member k j)
let gf k j = match member k j with `Float f -> f | `Int n -> float_of_int n | _ -> 0.
let present k j = match member k j with `Null -> false | _ -> true

let from_json path =
  let t = zero () in
  ignore
    (Corpus.iter_json path ~f:(fun repo ->
         t.repos <- t.repos + 1;
         t.owners <- t.owners + 1;
         t.stars <- t.stars + gi "stars" repo;
         if to_bool (member "is_private" repo) then
           t.private_repos <- t.private_repos + 1;
         t.topics <- t.topics + List.length (arr "topics" repo);
         List.iter
           (fun run ->
             t.runs <- t.runs + 1;
             List.iter
               (fun job ->
                 t.jobs <- t.jobs + 1;
                 t.queued <- t.queued + gi "queued_ms" job;
                 if present "exit_code" job then t.exit_codes <- t.exit_codes + 1;
                 t.labels <- t.labels + List.length (arr "labels" job);
                 List.iter
                   (fun st ->
                     t.steps <- t.steps + 1;
                     let ms = gi "duration_ms" st in
                     t.step_ms <- t.step_ms + ms;
                     t.log_bytes <- t.log_bytes + gi "log_bytes" st;
                     t.cost <- t.cost +. (float_of_int ms *. gf "cost_per_ms" st);
                     if present "error" st then t.errors <- t.errors + 1)
                   (arr "steps" job))
               (arr "jobs" run))
           (arr "runs" repo)));
  t

let one_int sql =
  match Data.fetch sql with
  | [ [ v ] ] -> Option.value (Pgx.Value.to_int v) ~default:(-1)
  | _ -> -1

let one_float sql =
  match Data.fetch sql with
  | [ [ v ] ] -> Option.value (Pgx.Value.to_float v) ~default:nan
  | _ -> nan

let from_sql () =
  let t = zero () in
  t.repos <- one_int "select count(*) from repository";
  t.owners <- one_int "select count(*) from owner";
  t.topics <- one_int "select count(*) from topic";
  t.runs <- one_int "select count(*) from run";
  t.jobs <- one_int "select count(*) from job";
  t.labels <- one_int "select count(*) from label";
  t.steps <- one_int "select count(*) from step";
  t.private_repos <- one_int "select count(*) from repository where is_private";
  t.stars <- one_int "select coalesce(sum(stars),0) from repository";
  t.queued <- one_int "select coalesce(sum(queued_ms),0) from job";
  t.step_ms <- one_int "select coalesce(sum(duration_ms),0) from step";
  t.log_bytes <- one_int "select coalesce(sum(log_bytes),0) from step";
  t.errors <- one_int "select count(*) from step where error is not null";
  t.exit_codes <- one_int "select count(*) from job where exit_code is not null";
  t.cost <- one_float "select coalesce(sum(duration_ms * cost_per_ms),0) from step";
  t

let () =
  (match List.tl (Array.to_list Sys.argv) with
  | "--corpus" :: v :: _ -> corpus := v
  | _ -> ());
  let j = from_json !corpus and s = from_sql () in
  let bad = ref 0 in
  let cmp name a b =
    let ok = a = b in
    if not ok then incr bad;
    Printf.printf "  %-16s %14d %14d  %s\n" name a b (if ok then "ok" else "DIFFER")
  in
  (* The float is summed in a different order on each side, so exact equality
     is the wrong test. A relative tolerance is the right one, and 1e-9 is far
     tighter than any real shredding mistake would land inside. *)
  let cmpf name a b =
    let ok = Float.abs (a -. b) <= 1e-9 *. Float.max 1. (Float.abs a) in
    if not ok then incr bad;
    Printf.printf "  %-16s %14.4f %14.4f  %s\n" name a b (if ok then "ok" else "DIFFER")
  in
  Printf.printf "\n  %-16s %14s %14s\n" "" "json" "postgres";
  print_endline (String.make 50 '-');
  cmp "repository" j.repos s.repos;
  cmp "owner" j.owners s.owners;
  cmp "topic" j.topics s.topics;
  cmp "run" j.runs s.runs;
  cmp "job" j.jobs s.jobs;
  cmp "label" j.labels s.labels;
  cmp "step" j.steps s.steps;
  print_endline (String.make 50 '-');
  cmp "private repos" j.private_repos s.private_repos;
  cmp "sum stars" j.stars s.stars;
  cmp "sum queued_ms" j.queued s.queued;
  cmp "sum step ms" j.step_ms s.step_ms;
  cmp "sum log_bytes" j.log_bytes s.log_bytes;
  cmp "steps w/ error" j.errors s.errors;
  cmp "jobs w/ exit" j.exit_codes s.exit_codes;
  cmpf "sum ms*cost" j.cost s.cost;
  print_endline (String.make 50 '-');
  if !bad = 0 then print_endline "  the two stores hold the same data\n"
  else Printf.printf "  %d disagreements\n\n" !bad;
  exit (if !bad = 0 then 0 else 1)
