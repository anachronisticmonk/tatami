(* run.mli *)

type t
type id = int
val make : id:int -> repo_id:Repo.id -> idx:int -> branch:string -> ms:int -> status:string -> trigger:string option -> t
val get : id -> t
val of_repo : Repo.id -> t list
val id : t -> int
val repo_id : t -> Repo.id
val idx : t -> int
val branch : t -> string
val ms : t -> int
val status : t -> string
val trigger : t -> string option
val set_id : t -> int -> t
val set_repo_id : t -> Repo.id -> t
val set_idx : t -> int -> t
val set_branch : t -> string -> t
val set_ms : t -> int -> t
val set_status : t -> string -> t
val set_trigger : t -> string option -> t
