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
type column = {name : string; layout: layout}

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

let layout_of_type = function
    | "int" -> Some (Plain (Dense Int))
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
          | [ "val"; name ], Some ("t", ret) ->
            Option.map (fun layout -> {name; layout})(layout_of_type ret)
          | _ -> None)

(*NOTE table name*)
let load path =
  let text = read_file path in
  let columns = List.filter_map parse_line (String.split_on_char '\n' text) in
  {table = Filename.remove_extension (Filename.basename path); columns}
