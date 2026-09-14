(* b.ml *)

type id = Ids.b
type t = { id : id; c : int; d : int }
let get _ = failwith "B.get: no row source"
let c r = r.c
let d r = r.d
