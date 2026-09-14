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

(* A uuid rather than a counter: a repo is the thing customers name and link
   to, so its identity has to be stable and unguessable. Storage-wise that
   makes it text -- variable width, no arithmetic, compared byte for byte --
   and every key pointing at it is text too. Runs, jobs and steps keep integer
   ids; they are only ever reached through their parent. *)
val id : t -> uuid
val name : t -> string
val org : t -> string
val is_private : t -> bool
