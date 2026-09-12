(* this file has the value of query so something like *)
(* select qty from orders where qty > 4 *)


(*TODO will worry about `join` later*)
type value =
  | Int of int
  | Float of float
  | Text of string

type op = Eq | Ne | Lt | Le | Gt | Ge

type predicate = {column : string; op : op; value : value}
type t = { table : string; select : string list; where : predicate option }

let op_to_string = function
    | Eq -> "=" | Ne -> "<>" | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">="

let value_to_string = function
    | Int n -> string_of_int n
    | Float f -> Printf.sprintf "%g" f
    | Text s -> "'" ^ s ^ "'"

let predicate_to_string p =
  Printf.sprintf "%s %s %s" p.column (op_to_string p.op)
    (value_to_string p.value)

(*incorporating select \* *)
let to_string q =
  Printf.sprintf "select %s from %s%s"
    (match q.select with [] -> "*" | cols -> String.concat ", " cols)
    q.table
    (match q.where with
     | None -> ""
     | Some p -> " where " ^ predicate_to_string p)
