(* What the signature licenses, for one query.

   Everything here is a function of the .mli and the query text, and of
   nothing else. That is the bet of the project narrowed to one function: we
   generated the layout, so the access shape is known without measuring it.
   Growing the corpus cannot change a plan, because no value of any row is
   consulted to build one.

   The value has to be honest about cost as well as licence, because [plain]
   and [tuned] are meant to be compared. [guarded] is a concession -- a test
   in the loop we could not get rid of. [Identity] is a win. A plan that only
   recorded the wins would make the differential look better than it is. *)

type filter =
  | Keep_all
  | Int_compare of {
      column : string;
      op : Query.op;
      operand : int;
      guarded : bool;
    }
  | Float_compare of {
      column : string;
      op : Query.op;
      operand : float;
      guarded : bool;
    }
  | Text_compare of {
      column : string;
      op : Query.op;
      operand : string;
      guarded : bool;
    }

type project =
  (*NOTE Gather allocated a fresh array and copied every element to produce something identical *)
  (*     Identity means nothing to gather as it is every row is surviving *)
  | Identity of string list
  | Gather of string list

type t = {
  read : string list;
  filter : filter;
  project : project;
}

exception Error of string

let fail fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt

(* Plain and Nullable differ in whether there is a mask, not in what the values
   look like, so the shape is what decides which comparison to emit and the
   constructor is what decides [guarded]. *)
let shape_of (l : Schema.layout) =
  match l with Schema.Plain s | Schema.Nullable s -> s

let nullable (c : Schema.column) =
  match c.layout with Schema.Nullable _ -> true | Schema.Plain _ -> false

let column (schema : Schema.t) name =
  match Schema.column schema name with
  | Some c -> c
  | None -> fail "no column %s in %s" name schema.table

(* [select *] is the whole table in signature order; anything else is the
   columns as written, because the output comes back in that order. *)
let projected (schema : Schema.t) (q : Query.t) =
  match q.select with [] -> Schema.names schema | cols -> cols

let dedup names =
  let rec go seen = function
    | [] -> []
    | n :: rest when List.mem n seen -> go seen rest
    | n :: rest -> n :: go (n :: seen) rest
  in
  go [] names

(* The predicate's column is read whether or not it is selected: [select note
   from orders where qty > 4] touches qty. *)
let read_of schema (q : Query.t) =
  dedup
    (projected schema q
    @ match q.where with None -> [] | Some p -> [ p.column ])

(* Compare-a-fixed-width-column-to-a-constant is the case the whole framing has
   to get right, so the dispatch is on the shape the signature states and not
   on anything observed. [guarded] comes from the constructor alone: a column
   the .mli declares total has no validity array, so the loop has nothing to
   test -- the test is not skipped, it is absent. *)
let filter_of schema (q : Query.t) =
  match q.where with
  | None -> Keep_all
  | Some p ->
      let c = column schema p.column in
      let column = c.name and op = p.op and guarded = nullable c in
      (match (shape_of c.layout, p.value) with
      | Schema.Dense Schema.Int, Query.Int operand ->
          Int_compare { column; op; operand; guarded }
      | Schema.Dense Schema.Float, Query.Float operand ->
          Float_compare { column; op; operand; guarded }
      (* The column is already inexact and the literal is exact, so widening
         costs nothing and [where price > 10] need not be written 10.0. *)
      | Schema.Dense Schema.Float, Query.Int n ->
          Float_compare { column; op; operand = float_of_int n; guarded }
      | Schema.Var, Query.Text operand ->
          Text_compare { column; op; operand; guarded }
      (* Everything below is refused rather than coerced. The signature is the
         authority on what a column holds, so a literal it cannot describe is
         a mistake in the query. [qty < 4.5] is the case that earns the rule:
         rounding to [qty < 4] silently drops the rows where qty = 4, which is
         answering wrongly and quickly -- the one failure this project cannot
         afford. *)
      | Schema.Dense Schema.Int, Query.Float f ->
          fail "%s is an int column and %g is not an int" column f
      | Schema.Dense Schema.Bool, _ ->
          fail "%s is a bool column, and there is no bool literal to compare it with yet"
            column
      | Schema.Dense (Schema.Int | Schema.Float), Query.Text s ->
          fail "%s is a number, so it cannot be compared with '%s'" column s
      | Schema.Var, (Query.Int _ | Query.Float _) ->
          fail "%s is a string column, so it cannot be compared with %s" column
            (Query.value_to_string p.value))

(* With no rows removed the selection is the identity, so there is nothing to
   gather: the output columns are the input arrays, copied nowhere. That is a
   larger win than anything the predicate offers, and it is invisible unless
   the projection is judged in its own right rather than as the tail of the
   filter. *)
let project_of cols = function
  | Keep_all -> Identity cols
  | Int_compare _ | Float_compare _ | Text_compare _ -> Gather cols

let plan (schema : Schema.t) (q : Query.t) =
  if q.table <> schema.table then
    fail "no table %s; this signature describes %s" q.table schema.table;
  let cols = projected schema q in
  (* Resolved here so an unknown column is an error while we still have the
     query to blame, rather than a failure inside a loop. *)
  List.iter (fun n -> ignore (column schema n)) cols;
  let filter = filter_of schema q in
  { read = read_of schema q; filter; project = project_of cols filter }

(* ---- rendering ---------------------------------------------------------- *)

(* Printed in the vocabulary of the loop that will run, not of the SQL that
   produced it -- [Query.to_string] already prints the query. The point of
   reading these side by side is to see what the signature added. *)

let mark guarded = if guarded then " (guarded)" else ""

let filter_to_string = function
  | Keep_all -> "keep all"
  | Int_compare { column; op; operand; guarded } ->
      Printf.sprintf "%s %s %d%s" column (Query.op_to_string op) operand
        (mark guarded)
  | Float_compare { column; op; operand; guarded } ->
      Printf.sprintf "%s %s %g%s" column (Query.op_to_string op) operand
        (mark guarded)
  | Text_compare { column; op; operand; guarded } ->
      Printf.sprintf "%s %s '%s'%s" column (Query.op_to_string op) operand
        (mark guarded)

let project_to_string = function
  | Identity cols -> "identity " ^ String.concat ", " cols
  | Gather cols -> "gather " ^ String.concat ", " cols

let to_string t =
  Printf.sprintf "read %s | filter %s | project %s"
    (String.concat ", " t.read)
    (filter_to_string t.filter)
    (project_to_string t.project)
