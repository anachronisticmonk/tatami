(* step_row.ml *)

let table = "step"
let columns = ["id"; "job_id"; "idx"; "error"; "ms"; "name"; "rate"]
let key ~doc = Bind.int (Json.int doc "id")
let row ~self ~parent ~pos ~doc =
  let r = Step.make ~id:Neutral.int ~job_id:Neutral.int ~idx:Neutral.int ~error:(Json.string_opt doc "error") ~ms:(Json.int doc "ms") ~name:(Json.string doc "name") ~rate:(Json.float doc "rate") in
  let r = Step.set_id r (Unbind.int self) in
  let r = Step.set_job_id r (Unbind.int parent) in
  let r = Step.set_idx r (Unbind.int pos) in
  [Bind.int (Step.id r); Bind.int (Step.job_id r); Bind.int (Step.idx r); Bind.string_opt (Step.error r); Bind.int (Step.ms r); Bind.string (Step.name r); Bind.float (Step.rate r)]
