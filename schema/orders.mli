(* Generated from the corpus by Phase 1 -- do not edit by hand.
   (Provisional: hand-written until Phase 1 emits the real thing.)

   Column order matches the table, so [select *] and the expansion this file
   licenses return the same columns in the same order. *)

type t
type id

val id : t -> id
val customer_id : t -> int
val sku : t -> string
val qty : t -> int
val price : t -> float
val note : t -> string option
