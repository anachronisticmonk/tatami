(* repo.ml *)

type uuid = string
type id = uuid
type t = { id : uuid; name : string; org : string; private_ : bool }
let make ~id ~name ~org ~private_ = { id; name; org; private_ }
let get _ = failwith "Repo.get: no row source"
let id r = r.id
let name r = r.name
let org r = r.org
let private_ r = r.private_
let set_id r v = { r with id = v }
let set_name r v = { r with name = v }
let set_org r v = { r with org = v }
let set_private_ r v = { r with private_ = v }
