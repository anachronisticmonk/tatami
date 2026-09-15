(* job_row.ml *)

let table = "job"
let columns = ["id"; "run_id"; "idx"; "exit"; "ms"; "os"; "status"]
let key ~doc = Bind.int (Json.int doc "id")
let row ~self ~parent ~pos ~doc =
  let r = Job.make ~id:Neutral.int ~run_id:Neutral.int ~idx:Neutral.int ~exit:(Json.int_opt doc "exit") ~ms:(Json.int doc "ms") ~os:(Json.string doc "os") ~status:(Json.string doc "status") in
  let r = Job.set_id r (Unbind.int self) in
  let r = Job.set_run_id r (Unbind.int parent) in
  let r = Job.set_idx r (Unbind.int pos) in
  [Bind.int (Job.id r); Bind.int (Job.run_id r); Bind.int (Job.idx r); Bind.int_opt (Job.exit r); Bind.int (Job.ms r); Bind.string (Job.os r); Bind.string (Job.status r)]
