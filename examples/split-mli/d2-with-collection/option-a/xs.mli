type id = Ids.xs
type t = { id : id; parent_id : Ids.root; idx : int; n : int }
val get : id -> t
