(* generated.mli *)

module B : sig
  type id
  type t = { id : id; c : int; d : int }
  val get : id -> t
end

module Root : sig
  type id
  type t = { id : id; a : int; b : B.id }
  val get : id -> t
  val b : t -> B.t
end
