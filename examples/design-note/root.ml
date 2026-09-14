(* root.ml *)

type id = Ids.root
type t = { id : id; a : int; b : B.id }
let get _ = failwith "Root.get: no row source"
let a r = r.a
let b r = B.get r.b
