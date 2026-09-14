(* root.mli *)

type id = Ids.root
type t = { id : id; a : int; b : B.id }
val get : id -> t
val a : t -> int
val b : t -> B.t
