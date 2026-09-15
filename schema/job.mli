(* job.mli *)

type t
type id = int
val make : id:int -> run_id:Run.id -> idx:int -> exit:int option -> ms:int -> os:string -> status:string -> t
val get : id -> t
val of_run : Run.id -> t list
val id : t -> int
val run_id : t -> Run.id
val idx : t -> int
val exit : t -> int option
val ms : t -> int
val os : t -> string
val status : t -> string
val set_id : t -> int -> t
val set_run_id : t -> Run.id -> t
val set_idx : t -> int -> t
val set_exit : t -> int option -> t
val set_ms : t -> int -> t
val set_os : t -> string -> t
val set_status : t -> string -> t
