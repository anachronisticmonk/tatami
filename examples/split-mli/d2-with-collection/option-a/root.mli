type id = Ids.root
type t = { id : id; a : int; b : B.id }
val get : id -> t
val b : t -> B.t                  (* follows the foreign key into table b *)
val xs : t -> Xs.t list           (* the rows of the collection at .xs *)
