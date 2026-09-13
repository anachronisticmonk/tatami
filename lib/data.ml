(*NOTE Data plane the actual numbers, sitting in arrays*)

type values =
  | Ints of int array
  | Floats of float array
  | Texts of string array

(*NOTE explain why we need to carry the valid *)
(* the idea is we can call at a column level *)
(* match column.valid with | None -> the fast loop | Some the guarded *)
(* loop valid.so we need that information and we *)
(* dont need need  *)
type t = {name : string; values: values; valid : bool array option}

let length c =
  match c.values with
  | Ints a -> Array.length a
  | Floats a -> Array.length a
  | Texts a -> Array.length a

(*NOTE always true for a column that has no validity array*)
let is_valid c i = match c.valid with None -> true | Some v -> v.(i)

(*NOTE printing utility if something is None => NULL*)
let cell c i =
  if not (is_valid c i) then None
  else
    Some
      (match c.values with
       | Ints a -> string_of_int a.(i)
       | Floats a -> Printf.sprintf "%.2f" a.(i)
       | Texts a -> a.(i)
      )

let find columns name =
  List.find_opt (fun c -> c.name = name) columns


(* loading from the datastore instead of  *)

module Pg = Pgx_unix

let env k default = match Sys.getenv_opt k with Some v -> v | None -> default
let host = env "TATAMI_PGHOST" "localhost"
let port = int_of_string (env "TATAMI_PGPORT" "5432")
let user = env "TATAMI_PGUSER" "tatami"
let password = env "TATAMI_PGPASSWORD" "tatami"
let database = env "TATAMI_PGDATABASE" "tatami"

let quote s = "\"" ^ s ^ "\""

(*TODO change this function when where and order by aggregate*)
let select_sql (schema : Schema.t) cols =
  Printf.sprintf "SELECT %s FROM %s"
    (String.concat ", "
       (List.map (fun (c: Schema.column) -> quote c.name) cols))
    (quote schema.table)

let count_sql (schema : Schema.t) =
  Printf.sprintf "SELECT count(*) FROM %s" (quote schema.table)

type slot = {values : values; valid : bool array option}

(*TODO can't this be done using some clever effect handler? *)
(* somewhere to put values as rows arrive so just a temporary staging thing *)

let slot n (c : Schema.column) =
  let shape, valid =
    match c.layout with
    | Schema.Plain s -> (s, None)
    | Schema.Nullable s -> (s, Some (Array.make n true))
  in
  let values =
    match shape with
    | Schema.Dense Schema.Int | Schema.Dense Schema.Bool -> Ints (Array.make n 0)
    | Schema.Dense Schema.Float -> Floats (Array.make n 0.)
    | Schema.Var -> Texts (Array.make n "")
  in
  {values; valid}

(*NOTE defining load and store*)
let store (c : Schema.column) slot i v =
  let present =
    match slot.values with
    | Ints a -> (
        match Pgx.Value.to_int v with
        | Some x ->
          a.(i) <- x;
          true
        | None -> false
      )
    | Floats a -> (
        match Pgx.Value.to_float v with
        | Some x ->
          a.(i) <- x;
          true
        | None -> false
      )
    | Texts a -> (
        match Pgx.Value.to_string v with
        | Some x ->
          a.(i) <- x;
          true
        | None -> false
      )
  in
  match slot.valid with
  | Some valid -> valid.(i) <- present
  | None ->
    if not present then failwith
        (Printf.sprintf "%s is NULL in the data, but its signature says otherwise"
           c.name)

(*wanted is a list of column names *)
(* slots is just a list, one per column *)
(* so List.iter2 f [a1;a2;a3] [b1;b2;b3] *)
(* becomes f a1 b1 fa2 b2 f a3 b3 returns () *)
(* and List.map2 becomes *)
(* [f a1 b1; fa2 b2; f a3 b3] *)
let load (schema : Schema.t) wanted =
  let cols =
    (*cols = [qty: int; note : string option] *)
    (* say n = 3 *)
    (* slots = [{values Ints [|0;0;0|]; valid = None]}, *)
    (*          {values Texts[|""; ""; ""|]; valid = Some [|t;t;t|]]]} ] *)
    (*          the slots[1] corresponds to the note and its Nullable *)
    (*          because its Some an Array *)
    (*          while the qty slot is valid = None *)
    List.map
      (fun n ->
         match Schema.column schema n with
         | Some c -> c
         | None -> failwith (Printf.sprintf "no column %s in %s" n schema.table))
      wanted
  in
  Pg.with_conn ~ssl:`No ~host ~port ~user ~password ~database (fun conn ->
      let n =
        match Pg.execute conn (count_sql schema) with
        | [ [ v ] ] -> Option.value (Pgx.Value.to_int v) ~default:0
        | _ -> 0
      in
      let slots = List.map (slot n) cols in
      let pairs = List.combine cols slots in
      (*(qty, slot_qty); (note, slot_note)*)
      let i = ref 0 in
      Pg.execute_iter conn (select_sql schema cols)
        ~f: (fun row ->
            List.iter2 (fun (c,s) v -> store c s !i v) pairs row;
            incr i);
      List.map2
        (fun (c : Schema.column) s ->
           { name = c.name; values = s.values; valid = s.valid })
        cols slots)

(* One round trip, for whoever asks. Both kernels go through here, so "they
   issue the same query against the same connection" is a property of the code
   rather than of two functions happening to agree. *)
let fetch sql =
  Pg.with_conn ~ssl:`No ~host ~port ~user ~password ~database (fun conn ->
      Pg.execute conn sql)

(* The same round trip, but the rows are handed over one at a time and never
   collected into a list. Whoever consumes them decides what to keep. *)
let fetch_iter sql ~f =
  Pg.with_conn ~ssl:`No ~host ~port ~user ~password ~database (fun conn ->
      Pg.execute_iter conn sql ~f)
