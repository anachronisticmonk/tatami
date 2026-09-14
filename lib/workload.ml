(* The questions, and what a store has to be able to answer.

   Both paths implement this signature, which is the point of having one: a
   benchmark where each side answers a question shaped to suit it measures
   nothing. The answers are compared before the timings are believed.

   The five were chosen to have a crossover in them rather than to flatter
   columns. [document] is the case a row store exists for: everything under one
   repository, which row-major already holds contiguously and which the
   columnar side has to reassemble by scanning three tables. If columns won
   that one too the benchmark would be wrong somewhere. *)

type answer =
  | Count of int
  | Sum_int of int
  | Sum_float of float
  | Groups of (string * int) list  (* sorted, so two stores compare equal *)
  | Row of string list
  | Missing

let equal a b =
  match (a, b) with
  (* Summed in a different order on each side, so exact equality is the wrong
     test on the float. Everything else is integral and must match exactly. *)
  | Sum_float x, Sum_float y ->
      Float.abs (x -. y) <= 1e-9 *. Float.max 1. (Float.abs x)
  | x, y -> x = y

let to_string = function
  | Count n -> Printf.sprintf "count %d" n
  | Sum_int n -> Printf.sprintf "sum %d" n
  | Sum_float f -> Printf.sprintf "sum %.4f" f
  | Groups g ->
      String.concat ", " (List.map (fun (k, v) -> Printf.sprintf "%s=%d" k v) g)
  | Row r -> String.concat " | " r
  | Missing -> "missing"

module type STORE = sig
  val name : string

  (* The materialised corpus. What this is, is the whole experiment. *)
  type t

  (* Everything each path pays before it can answer anything: parsing,
     shredding, allocating. Timed and reported separately, because a store that
     is fast to query and slow to build has not obviously won. *)
  val load : string -> t

  (* How much the store is holding, to keep the comparison honest about memory
     as well as time. Words, as the GC counts them. *)
  val footprint : t -> float

  (* Everything under one repository: how many runs, jobs and steps it has and
     their total duration. Row-major holds that subtree contiguously and walks
     it; the columnar side has no repository-shaped thing at all and must find
     the runs, then their jobs, then their steps. The case columns should lose. *)
  val document : t -> string -> answer

  (* How many steps ran longer than [ms]. A scan of one column out of ten. *)
  val scan : t -> int -> answer

  (* sum(duration_ms * cost_per_ms) over steps longer than [ms]. Two columns,
     arithmetic, and a computed result -- the query the first attempt never
     implemented and the one the layouts should separate on. *)
  val computed : t -> int -> answer

  (* The longest step under each status. Five groups over the whole table. *)
  val by_status : t -> answer

  (* Total step duration for one organisation: step -> job -> run ->
     repository, which is the three hops the corpus exists to force. *)
  val three_hop : t -> string -> answer
end
