(* repo.mli *)

type uuid = string
type t
type id = uuid
val make : id:uuid -> name:string -> org:string -> private_:bool -> t
val get : id -> t
val id : t -> uuid
val name : t -> string
val org : t -> string
val private_ : t -> bool
val set_id : t -> uuid -> t
val set_name : t -> string -> t
val set_org : t -> string -> t
val set_private_ : t -> bool -> t
