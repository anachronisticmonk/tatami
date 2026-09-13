(* Generated from the corpus by Phase 1 -- do not edit by hand.

   Was the array at repository.runs. [repository_id] and [idx] are the two
   columns every element table carries: which parent, and where in the array. *)

type t
type id

val id : t -> id
val repository_id : t -> Repository.id
val idx : t -> int
val number : t -> int
val commit_sha : t -> string
val branch : t -> string
val status : t -> string
val started_at : t -> int
val duration_ms : t -> int
val trigger : t -> string option
