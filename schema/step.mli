(* Generated from the corpus by Phase 1 -- do not edit by hand.

   One command inside a job. Three hops from the root and by far the largest
   table.

   [ms] is how long it ran and [rate] is what a millisecond costs on that
   runner, so [ms * rate] is what the step cost. Both are total, so the product
   is known to need no validity array before a single row is read -- which is
   the one thing a database catalog cannot tell you about it, there being no
   such column for it to describe. *)

type t
type id

val id : t -> id
val job_id : t -> Job.id
val idx : t -> int
val name : t -> string
val ms : t -> int
val rate : t -> float
val error : t -> string option
