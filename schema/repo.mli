(* repo.mli *)

type uuid = string
type t
type id
val get : id -> t
val id : t -> uuid
val name : t -> string
val org : t -> string
val private_ : t -> bool
