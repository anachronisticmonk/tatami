type id
type t = { id : id; parent_id : Root.id; idx : int; n : int }
val get : id -> t
val of_root : Root.id -> t list   (* the rows whose parent_id is this root *)
