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
  mutable runs : int;
  mutable jobs : int;
  mutable steps : int;
  mutable private_repos : int;
  mutable run_ms : int;
  mutable job_ms : int;
  mutable step_ms : int;
  mutable errors : int;
  mutable exits : int;
  mutable triggers : int;
  mutable cost : float;
}

let zero () =
  { repos = 0; runs = 0; jobs = 0; steps = 0; private_repos = 0; run_ms = 0;
    job_ms = 0; step_ms = 0; errors = 0; exits = 0; triggers = 0; cost = 0. }

let arr k j = match member k j with `List l -> l | _ -> []
let gi k j = to_int (member k j)
let gf k j = match member k j with `Float f -> f | `Int n -> float_of_int n | _ -> 0.
let present k j = match member k j with `Null -> false | _ -> true

let from_json path =
  let t = zero () in
  ignore
    (Corpus.iter_json path ~f:(fun repo ->
         t.repos <- t.repos + 1;
         if to_bool (member "private" repo) then
           t.private_repos <- t.private_repos + 1;
         List.iter
           (fun run ->
             t.runs <- t.runs + 1;
             t.run_ms <- t.run_ms + gi "ms" run;
             if present "trigger" run then t.triggers <- t.triggers + 1;
             List.iter
               (fun job ->
                 t.jobs <- t.jobs + 1;
                 t.job_ms <- t.job_ms + gi "ms" job;
                 if present "exit" job then t.exits <- t.exits + 1;
                 List.iter
                   (fun st ->
                     t.steps <- t.steps + 1;
                     let ms = gi "ms" st in
                     t.step_ms <- t.step_ms + ms;
                     t.cost <- t.cost +. (float_of_int ms *. gf "rate" st);
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
  t.repos <- one_int "select count(*) from repo";
  t.runs <- one_int "select count(*) from run";
  t.jobs <- one_int "select count(*) from job";
  t.steps <- one_int "select count(*) from step";
  t.private_repos <- one_int "select count(*) from repo where is_private";
  t.run_ms <- one_int "select coalesce(sum(ms),0) from run";
  t.job_ms <- one_int "select coalesce(sum(ms),0) from job";
  t.step_ms <- one_int "select coalesce(sum(ms),0) from step";
  t.errors <- one_int "select count(*) from step where error is not null";
  t.exits <- one_int "select count(*) from job where exit is not null";
  t.triggers <- one_int "select count(*) from run where trigger is not null";
  t.cost <- one_float "select coalesce(sum(ms * rate),0) from step";
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
  cmp "repo" j.repos s.repos;
  cmp "run" j.runs s.runs;
  cmp "job" j.jobs s.jobs;
  cmp "step" j.steps s.steps;
  print_endline (String.make 50 '-');
  cmp "private repos" j.private_repos s.private_repos;
  cmp "sum run ms" j.run_ms s.run_ms;
  cmp "sum job ms" j.job_ms s.job_ms;
  cmp "sum step ms" j.step_ms s.step_ms;
  cmp "steps w/ error" j.errors s.errors;
  cmp "jobs w/ exit" j.exits s.exits;
  cmp "runs w/ trigger" j.triggers s.triggers;
  cmpf "sum ms*rate" j.cost s.cost;
  print_endline (String.make 50 '-');
  if !bad = 0 then print_endline "  the two stores hold the same data\n"
  else Printf.printf "  %d disagreements\n\n" !bad;
  exit (if !bad = 0 then 0 else 1)
