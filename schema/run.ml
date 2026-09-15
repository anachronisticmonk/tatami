(* run.ml *)

type id = int
type t = { id : int; repo_id : Repo.id; idx : int; branch : string; ms : int; status : string; trigger : string option }
let make ~id ~repo_id ~idx ~branch ~ms ~status ~trigger = { id; repo_id; idx; branch; ms; status; trigger }
let get _ = failwith "Run.get: no row source"
let of_repo _ = failwith "Run.of_repo: no row source"
let id r = r.id
let repo_id r = r.repo_id
let idx r = r.idx
let branch r = r.branch
let ms r = r.ms
let status r = r.status
let trigger r = r.trigger
let set_id r v = { r with id = v }
let set_repo_id r v = { r with repo_id = v }
let set_idx r v = { r with idx = v }
let set_branch r v = { r with branch = v }
let set_ms r v = { r with ms = v }
let set_status r v = { r with status = v }
let set_trigger r v = { r with trigger = v }
