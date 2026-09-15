(* job.ml *)

type id = int
type t = { id : int; run_id : Run.id; idx : int; exit : int option; ms : int; os : string; status : string }
let make ~id ~run_id ~idx ~exit ~ms ~os ~status = { id; run_id; idx; exit; ms; os; status }
let get _ = failwith "Job.get: no row source"
let of_run _ = failwith "Job.of_run: no row source"
let id r = r.id
let run_id r = r.run_id
let idx r = r.idx
let exit r = r.exit
let ms r = r.ms
let os r = r.os
let status r = r.status
let set_id r v = { r with id = v }
let set_run_id r v = { r with run_id = v }
let set_idx r v = { r with idx = v }
let set_exit r v = { r with exit = v }
let set_ms r v = { r with ms = v }
let set_os r v = { r with os = v }
let set_status r v = { r with status = v }
