(* Generated from the corpus by Phase 1 -- do not edit by hand.

   Was the array at repository.runs.jobs.steps, three hops from the root and
   the largest table in the corpus.

   [duration_ms] is an int and [cost_per_ms] a float, both total. Their product
   is therefore known to need no validity array before a single row is read,
   which is the one claim a catalog cannot make about a computed column -- it
   has no column to describe. *)

type t
type id

val id : t -> id
val job_id : t -> Job.id
val idx : t -> int
val name : t -> string
val status : t -> string
val duration_ms : t -> int
val cost_per_ms : t -> float
val log_bytes : t -> int
val memory_mb : t -> int
val error : t -> string option
