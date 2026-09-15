(* repo_row.ml *)

let table = "repo"
let columns = ["id"; "name"; "org"; "private_"]
let key ~doc = Bind.uuid (Json.uuid doc "id")
let row ~self ~parent ~pos ~doc =
  let _ = parent in
  let _ = pos in
  let r = Repo.make ~id:Neutral.uuid ~name:(Json.string doc "name") ~org:(Json.string doc "org") ~private_:(Json.bool doc "private") in
  let r = Repo.set_id r (Unbind.uuid self) in
  [Bind.uuid (Repo.id r); Bind.string (Repo.name r); Bind.string (Repo.org r); Bind.bool (Repo.private_ r)]
