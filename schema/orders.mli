(* Generated from the corpus by Phase 1 -- do not edit by hand.
   (Provisional: hand-written until Phase 1 emits the real thing.) *)

type t
type id

val id    : t -> id
val qty   : t -> int
val price : t -> float
val sku   : t -> string
val note  : t -> string option
