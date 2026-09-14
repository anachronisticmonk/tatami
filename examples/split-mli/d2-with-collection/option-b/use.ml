(* Both directions of the foreign key, type-checked against the .cmi files. *)
let children (r : Root.t) : Xs.t list = Xs.of_root r.Root.id
let owner (x : Xs.t) : Root.t = Root.get x.Xs.parent_id
