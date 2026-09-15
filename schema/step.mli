(* step.mli *)

type t
type id = int
val make : id:int -> job_id:Job.id -> idx:int -> error:string option -> ms:int -> name:string -> rate:float -> t
val get : id -> t
val of_job : Job.id -> t list
val id : t -> int
val job_id : t -> Job.id
val idx : t -> int
val error : t -> string option
val ms : t -> int
val name : t -> string
val rate : t -> float
val set_id : t -> int -> t
val set_job_id : t -> Job.id -> t
val set_idx : t -> int -> t
val set_error : t -> string option -> t
val set_ms : t -> int -> t
val set_name : t -> string -> t
val set_rate : t -> float -> t
