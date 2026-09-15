(* run.mli *)

type t
type id
val get : id -> t
val id : t -> int
val repo_id : t -> Repo.id
val idx : t -> int
val of_repo : Repo.id -> t list
val branch : t -> string
val ms : t -> int
val status : t -> string
val trigger : t -> string option
