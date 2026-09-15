(* step.ml *)

type id = int
type t = { id : int; job_id : Job.id; idx : int; error : string option; ms : int; name : string; rate : float }
let make ~id ~job_id ~idx ~error ~ms ~name ~rate = { id; job_id; idx; error; ms; name; rate }
let get _ = failwith "Step.get: no row source"
let of_job _ = failwith "Step.of_job: no row source"
let id r = r.id
let job_id r = r.job_id
let idx r = r.idx
let error r = r.error
let ms r = r.ms
let name r = r.name
let rate r = r.rate
let set_id r v = { r with id = v }
let set_job_id r v = { r with job_id = v }
let set_idx r v = { r with idx = v }
let set_error r v = { r with error = v }
let set_ms r v = { r with ms = v }
let set_name r v = { r with name = v }
let set_rate r v = { r with rate = v }
