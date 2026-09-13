(* Generated from the corpus by Phase 1 -- do not edit by hand.

   Was the nested object at repository.owner. One row per repository, reached
   from the parent's [owner_id] rather than pointing back at it: a [ref] is a
   key the parent holds, not an element in a collection. *)

type t
type id

val id : t -> id
val login : t -> string
val kind : t -> string
val followers : t -> int
val email : t -> string option
