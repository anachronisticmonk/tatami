(* Generated from the corpus by Phase 1 -- do not edit by hand.
   (Provisional: hand-written until Phase 1 emits the real thing.)

   A project someone is building. The root: every other table reaches it by
   following keys back up.

   The JSON field is "private", which is an OCaml keyword and cannot be an
   accessor name, so Phase 1 mangles it. That mangling is the thing
   Proofs/Mangle.lean proves injective -- two distinct JSON keys can never
   collide into one field name, which is what makes the renaming safe rather
   than merely convenient. *)

type t
type id

val id : t -> id
val name : t -> string
val org : t -> string
val is_private : t -> bool
