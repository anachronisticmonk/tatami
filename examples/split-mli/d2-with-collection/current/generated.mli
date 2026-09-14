(* generated.mli *)

module rec Xs : sig
  type id
  type t = { id : id; parent_id : Root.id; idx : int; n : int }
  val get : id -> t
end

and B : sig
  type id
  type t = { id : id; c : int; d : int }
  val get : id -> t
end

and Root : sig
  type id
  type t = { id : id; a : int; b : B.id }
  val get : id -> t
  val b : t -> B.t
  val xs : t -> Xs.t list
end
