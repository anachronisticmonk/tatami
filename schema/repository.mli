(* Generated from the corpus by Phase 1 -- do not edit by hand.
   (Provisional: hand-written until Phase 1 emits the real thing.)

   The root table. [owner] was a nested object in the JSON, so it became a
   table of its own and this one holds a key into it -- the Lean model's
   [ref]. [topics] and [runs] were arrays, so they hold no column here at
   all: their elements point back, which is [coll]. *)

type t
type id

val id : t -> id
val name : t -> string
val org : t -> string
val default_branch : t -> string
val is_private : t -> bool
val stars : t -> int
val created_at : t -> int
val description : t -> string option
val owner_id : t -> Owner.id
