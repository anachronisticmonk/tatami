(* b.mli *)

type id = Ids.b
type t = { id : id; c : int; d : int }
val get : id -> t
val c : t -> int
val d : t -> int
