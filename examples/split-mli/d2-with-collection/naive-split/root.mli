type id
type t = { id : id; a : int; b : B.id }
val get : id -> t
val b : t -> B.t
val xs : t -> Xs.t list
