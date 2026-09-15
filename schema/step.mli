(* step.mli *)

type t
type id
val get : id -> t
val id : t -> int
val job_id : t -> Job.id
val idx : t -> int
val of_job : Job.id -> t list
val error : t -> string option
val ms : t -> int
val name : t -> string
val rate : t -> float
