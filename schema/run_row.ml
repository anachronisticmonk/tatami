(* run_row.ml *)

let table = "run"
let columns = ["id"; "repo_id"; "idx"; "branch"; "ms"; "status"; "trigger"]
let key ~doc = Bind.int (Json.int doc "id")
let row ~self ~parent ~pos ~doc =
  let r = Run.make ~id:Neutral.int ~repo_id:Neutral.uuid ~idx:Neutral.int ~branch:(Json.string doc "branch") ~ms:(Json.int doc "ms") ~status:(Json.string doc "status") ~trigger:(Json.string_opt doc "trigger") in
  let r = Run.set_id r (Unbind.int self) in
  let r = Run.set_repo_id r (Unbind.uuid parent) in
  let r = Run.set_idx r (Unbind.int pos) in
  [Bind.int (Run.id r); Bind.uuid (Run.repo_id r); Bind.int (Run.idx r); Bind.string (Run.branch r); Bind.int (Run.ms r); Bind.string (Run.status r); Bind.string_opt (Run.trigger r)]
