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

  (* Neither of these is emitted by the generator, nor in the design note.
     Without some way in, `id` is abstract and nothing can produce the first
     one, so a consumer cannot call `get` at all. *)
  val all : unit -> t list

  (* Entry by a key you are holding from outside -- a URL, another system.
     It returns an option because an arbitrary int need not name a row, which
     is exactly what `get` is spared by only accepting ids already in
     circulation. *)
  val find : int -> t option
end
