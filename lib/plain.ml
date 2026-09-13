(* The baseline: turn the query into SQL, hit the database, return the rows.

   No [Schema.t], no [Analysis.t], no layout. That is the experiment -- what
   separates this from [tuned] is the signature and nothing else.

   Note there is no validity array here. A mask is something you need when you
   have decided to hold a column as a dense array; these rows carry their own
   absence, one cell at a time, and [None] is a NULL. Not needing one is not an
   optimisation, it is what row-major storage gives you for free -- and paying
   for it per cell forever is what it charges in return. *)

(*TODO the literal is pasted into the SQL text, and [Query.value_to_string]
   is a display function that does not re-escape the quote the lexer already
   unescaped: [where sku = 'a''b'] emits [= 'a'b'], which is a syntax error and
   an injection. The fix is a pgx parameter -- WHERE "sku" = $1 with ~params --
   not a cleverer quoter. *)
let sql (q : Query.t) =
  Printf.sprintf "SELECT %s FROM %s%s"
    (match q.select with
    | [] -> "*"
    | cols -> String.concat ", " (List.map Data.quote cols))
    (Data.quote q.table)
    (match q.where with
    | None -> ""
    | Some p ->
        Printf.sprintf " WHERE %s %s %s" (Data.quote p.column)
          (Query.op_to_string p.op)
          (Query.value_to_string p.value))

(* One row per list, one cell per entry, [None] where the column was NULL. *)
let run_materialised (q : Query.t) =
  Data.fetch (sql q) |> List.map (List.map Pgx.Value.to_string)

(* Streamed, so the raw rows and the converted ones are never both alive. That
   much is available without a signature, and [tuned] must be measured against
   it rather than against the version that keeps two copies -- otherwise the
   .mli gets credit for something streaming did.

   What is still not available: storing a value without first knowing its type.
   Each cell arrives, becomes a boxed [string option], and is kept as one. *)
let run (q : Query.t) =
  let acc = ref [] in
  Data.fetch_iter (sql q) ~f:(fun row -> acc := List.map Pgx.Value.to_string row :: !acc);
  List.rev !acc

(* ---- querying what was already fetched ---------------------------------- *)

(* The load-once/query-many workload, [plain]'s half.

   Note what the rows do not carry: names. A [Data.t] knows it is "qty"; a list
   of cells knows only that it has a third element. So the column list has to be
   handed in from the SELECT that produced these rows -- and for [select *] there
   is nothing to hand in, because nothing here ever learned what came back. *)

let index names name =
  let rec go i = function
    | [] -> failwith (Printf.sprintf "no column %s in these rows" name)
    | n :: _ when String.equal n name -> i
    | _ :: rest -> go (i + 1) rest
  in
  go 0 names

let holds op c =
  match op with
  | Query.Eq -> c = 0
  | Query.Ne -> c <> 0
  | Query.Lt -> c < 0
  | Query.Le -> c <= 0
  | Query.Gt -> c > 0
  | Query.Ge -> c >= 0

(* Per row: reach the cell, decide what it is, parse it, compare. The parse is
   the whole story -- the text was already turned into a number once to answer
   the last query, and will be again for the next one. *)
let compare_cell (v : Query.value) cell =
  match cell with
  | None -> None
  | Some s -> (
      match v with
      | Query.Int n -> ( try Some (compare (int_of_string s) n) with _ -> None)
      | Query.Float f -> ( try Some (compare (float_of_string s) f) with _ -> None)
      | Query.Text t -> Some (compare s t))

let query names (q : Query.t) rows =
  let kept =
    match q.where with
    | None -> rows
    | Some p ->
        let j = index names p.column in
        List.filter
          (fun row ->
            match compare_cell p.value (List.nth row j) with
            | Some c -> holds p.op c
            | None -> false)
          rows
  in
  match q.select with
  | [] -> kept
  | cols ->
      let js = List.map (index names) cols in
      List.map (fun row -> List.map (List.nth row) js) kept
