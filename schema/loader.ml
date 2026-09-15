(* loader.ml *)

let tables = ["repo"; "run"; "job"; "step"]
let root = "repo"
let ddl = ["create table \"repo\" (\n  \"id\" uuid not null,\n  \"name\" text not null,\n  \"org\" text not null,\n  \"private_\" boolean not null,\n  primary key (\"id\")\n)"; "create table \"run\" (\n  \"id\" integer not null,\n  \"repo_id\" uuid not null,\n  \"idx\" integer not null,\n  \"branch\" text not null,\n  \"ms\" integer not null,\n  \"status\" text not null,\n  \"trigger\" text,\n  primary key (\"id\")\n)"; "create table \"job\" (\n  \"id\" integer not null,\n  \"run_id\" integer not null,\n  \"idx\" integer not null,\n  \"exit\" integer,\n  \"ms\" integer not null,\n  \"os\" text not null,\n  \"status\" text not null,\n  primary key (\"id\")\n)"; "create table \"step\" (\n  \"id\" integer not null,\n  \"job_id\" integer not null,\n  \"idx\" integer not null,\n  \"error\" text,\n  \"ms\" integer not null,\n  \"name\" text not null,\n  \"rate\" double precision not null,\n  primary key (\"id\")\n)"]
let constraints = ["alter table \"run\" add constraint \"run_repo_id_fkey\" foreign key (\"repo_id\") references \"repo\" (\"id\")"; "create index \"run_repo_id_idx\" on \"run\" (\"repo_id\")"; "alter table \"job\" add constraint \"job_run_id_fkey\" foreign key (\"run_id\") references \"run\" (\"id\")"; "create index \"job_run_id_idx\" on \"job\" (\"run_id\")"; "alter table \"step\" add constraint \"step_job_id_fkey\" foreign key (\"job_id\") references \"job\" (\"id\")"; "create index \"step_job_id_idx\" on \"step\" (\"job_id\")"]
let columns t =
  match t with
  | "repo" -> Repo_row.columns
  | "run" -> Run_row.columns
  | "job" -> Job_row.columns
  | "step" -> Step_row.columns
  | _ -> []
let keyed t =
  match t with
  | "repo" -> false
  | "run" -> false
  | "job" -> false
  | "step" -> false
  | _ -> false
let mints t =
  match t with
  | "repo" -> false
  | "run" -> false
  | "job" -> false
  | "step" -> false
  | _ -> false
let child_members t =
  match t with
  | "repo" -> ["runs"]
  | "run" -> ["jobs"]
  | "job" -> ["steps"]
  | "step" -> []
  | _ -> []
let child_tables t =
  match t with
  | "repo" -> ["run"]
  | "run" -> ["job"]
  | "job" -> ["step"]
  | "step" -> []
  | _ -> []
let ref_members t =
  match t with
  | "repo" -> []
  | "run" -> []
  | "job" -> []
  | "step" -> []
  | _ -> []
let ref_tables t =
  match t with
  | "repo" -> []
  | "run" -> []
  | "job" -> []
  | "step" -> []
  | _ -> []
let key t ~doc =
  match t with
  | "repo" -> Repo_row.key ~doc:doc
  | "run" -> Run_row.key ~doc:doc
  | "job" -> Job_row.key ~doc:doc
  | "step" -> Step_row.key ~doc:doc
  | _ -> Pgx.Value.null
let row t ~self ~parent ~pos ~doc =
  match t with
  | "repo" -> Repo_row.row ~self:self ~parent:parent ~pos:pos ~doc:doc
  | "run" -> Run_row.row ~self:self ~parent:parent ~pos:pos ~doc:doc
  | "job" -> Job_row.row ~self:self ~parent:parent ~pos:pos ~doc:doc
  | "step" -> Step_row.row ~self:self ~parent:parent ~pos:pos ~doc:doc
  | _ -> []
