(* Generated from the corpus by Phase 1 -- do not edit by hand.

   One build of a repo, triggered by a commit. Was the array at repo.runs, so
   it carries the two columns every element table carries: which parent, and
   what position it held in the array.

   [trigger] is optional because the JSON sometimes omits it and sometimes
   sets it to null. Both mean the same thing. *)

type t
type id

val id : t -> id
val repo_id : t -> Repo.id
val idx : t -> int
val branch : t -> string
val status : t -> string
val ms : t -> int
val trigger : t -> string option
