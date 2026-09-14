(* Generated from the corpus by Phase 1 -- do not edit by hand.

   One machine's share of a run. Two hops from the root, and the only route
   back to a repo is through [run_id] -- which is what makes a join across the
   nesting unavoidable rather than an optional optimisation. *)

type t
type id

val id : t -> id
val run_id : t -> Run.id
val idx : t -> int
val os : t -> string
val status : t -> string
val ms : t -> int
val exit : t -> int option
