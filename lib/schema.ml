(* defining some scalar types *)
(* TODO maybe expand these later *)
type scalar =
  | Int (*an int array: unboxed machine comparison*)
  | Float
  | Bool

(*NOTE a column can either be something like base + i * width Dense *)
(*     or can be offsets[i] *)
type shape =
  | Dense of scalar (* say an array of equal strides  *)
  | Var (* something like varchar and also doesnt have fixed width *)

(*either way this is a nice abstraction as option option int cannot exist from *)
(*  JSON *)
(* instead of nullable of layout we move the structure in shape which is either *)
(*  a Dense or Var *)
type layout =
  | Plain of shape (* this takes into account int *)
  | Nullable of shape (* this takes into account option int *)

(* one .mli descirbes one table so reading order.mli produces one of these *)
(* when join arrives a schema would become a list of them *)
(*NOTE [refers_to] is which table a key points into -- the only thing a join
  needs, and the one thing the storage type would have thrown away. It is kept
  beside the layout rather than inside it because a key's *storage* and its
  *target* are independent: repo.id is a uuid and so run.repo_id is text, while
  job.id is an int and so step.job_id is dense. *)
type column = {name : string; layout: layout; refers_to : string option}

type t = {table : string; columns: column list}

(*NOTE given a table and column name I would return the column corresponding *)
(*  to that name; None if the table has no such column *)
let column t name = List.find_opt (fun c -> c.name = name) t.columns
(* given a table, it will give you all column names *)
let names t = List.map (fun c -> c.name) t.columns

let scalar_to_string = function Int -> "int" | Float -> "float" | Bool -> "bool"
let shape_to_string  = function Dense s -> scalar_to_string s | Var -> "string"

let layout_to_string = function
  | Plain s -> shape_to_string s
  | Nullable s -> shape_to_string s ^ " option"


let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally: (fun () -> close_in ic)
    (fun () -> really_input_string ic (in_channel_length ic))

(*NOTE the idea is t -> option int should become *)
(* (t, option int) *)
let split_arrow s =
  let n = String.length s in
  let rec go i =
    if i + 1 >= n then None
    else if s.[i] = '-' && s.[i+1] = '>' then
      Some
        ( String.trim (String.sub s 0 i),
          String.trim (String.sub s (i + 2) (n - i - 2)))
    else go (i + 1)
  in
  go 0

(*NOTE [Repo.id] is a key into the repo table. Phase 1 writes the reference
  into the type rather than leaving it to a naming convention, so the schema
  reader can see it without being told which columns are keys.

  The layout cannot be settled here: it is whatever the *target's* id column
  is, and that lives in another file. [load_dir] resolves it. Until then a key
  is left as a dense int, which is right for every key except one. *)
let key_of_type s =
  let n = String.length s in
  if n > 3 && String.sub s (n - 3) 3 = ".id" then
    let m = String.sub s 0 (n - 3) in
    if m <> "" && m.[0] >= 'A' && m.[0] <= 'Z' && not (String.contains m '.') then
      Some (String.lowercase_ascii m)
    else None
  else None

let layout_of_type s =
  match s with
    | "int" -> Some (Plain (Dense Int))
    (*NOTE a uuid is text as far as storage is concerned: variable width, no
      arithmetic, compared by bytes. That it means something to a human is not
      a fact about the column. *)
    | "uuid" -> Some (Plain Var)
    | "float" -> Some (Plain (Dense Float))
    | "bool" -> Some (Plain (Dense Bool))
    | "string" -> Some (Plain Var)
    | "id" -> Some (Plain (Dense Int))
    | "int option" -> Some (Nullable (Dense Int))
    | "float option" -> Some (Nullable (Dense Float))
    | "bool option" -> Some (Nullable (Dense Bool))
    | "string option" -> Some (Nullable Var)
    | _ -> None

(*NOTE we need [val qty : t -> int] should become a column*)
(*NOTE this return Some {name = "qty"; layout = Plain (Dense Int)}*)

let parse_line line =
  let line = String.trim line in
  match String.index_opt line ':' with
  | None -> None
  | Some i -> (
      let lhs = String.trim (String.sub line 0 i) in
      let rhs =
        String.trim (String.sub line (i + 1) (String.length line - i - 1))
          in
          match (String.split_on_char ' ' lhs, split_arrow rhs) with
          | [ "val"; name ], Some ("t", ret) -> (
            match key_of_type ret with
            | Some table ->
              (* layout provisional; load_dir adopts the target's *)
              Some {name; layout = Plain (Dense Int); refers_to = Some table}
            | None ->
              Option.map
                (fun layout -> {name; layout; refers_to = None})
                (layout_of_type ret))
          | _ -> None)

(*NOTE table name*)
let load path =
  let text = read_file path in
  let columns = List.filter_map parse_line (String.split_on_char '\n' text) in
  {table = Filename.remove_extension (Filename.basename path); columns}


let table tables name = List.find_opt (fun t -> t.table = name) tables

(*NOTE a key is stored the way the thing it points at is stored. Resolved once
  the whole directory is read, because the answer is in another file. *)
let resolve tables =
  let id_layout name =
    match table tables name with
    | None -> None
    | Some t -> Option.map (fun c -> c.layout) (column t "id")
  in
  List.map
    (fun t ->
      { t with
        columns =
          List.map
            (fun c ->
              match c.refers_to with
              | None -> c
              | Some target -> (
                  match id_layout target with
                  | Some l -> {c with layout = l}
                  | None -> c))
            t.columns })
    tables

(*NOTE one .mli is one table, so a corpus of seven tables is seven files read
  together. Order is the directory's, sorted, so a schema is the same however
  the filesystem chooses to list it. *)
let load_dir dir =
  Sys.readdir dir |> Array.to_list
  |> List.filter (fun f -> Filename.check_suffix f ".mli")
  |> List.sort compare
  |> List.map (fun f -> load (Filename.concat dir f))
  |> resolve

(*NOTE the table a key points into, given the column that holds it. *)
let target c = c.refers_to

