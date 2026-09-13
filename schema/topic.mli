(* Generated from the corpus by Phase 1 -- do not edit by hand.

   Was the array of strings at repository.topics. A scalar array still becomes
   a table: the element needs somewhere to live and the order has to survive,
   so [idx] carries the position it had in the JSON. *)

type t
type id

val id : t -> id
val repository_id : t -> Repository.id
val idx : t -> int
val value : t -> string
