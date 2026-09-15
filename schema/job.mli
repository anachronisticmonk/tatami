(* job.mli *)

type t
type id
val get : id -> t
val id : t -> int
val run_id : t -> Run.id
val idx : t -> int
val of_run : Run.id -> t list
val exit : t -> int option
val ms : t -> int
val os : t -> string
val status : t -> string
