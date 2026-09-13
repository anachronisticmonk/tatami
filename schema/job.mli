(* Generated from the corpus by Phase 1 -- do not edit by hand.

   Was the array at repository.runs.jobs. Two hops from the root, and the only
   way back to a repository is through [run_id] -- which is what makes a join
   across the nesting unavoidable rather than an optional optimisation. *)

type t
type id

val id : t -> id
val run_id : t -> Run.id
val idx : t -> int
val name : t -> string
val runner_os : t -> string
val status : t -> string
val duration_ms : t -> int
val queued_ms : t -> int
val exit_code : t -> int option
