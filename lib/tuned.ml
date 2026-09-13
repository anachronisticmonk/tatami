(* The same query, the same SQL, the same rows back -- decoded by something
   that has read the .mli.

   Postgres does the filtering for both kernels, so the database work, the
   bytes on the wire and the result set are identical. What differs is only
   what those rows become in memory, and the .mli is the only input to that
   decision:

     qty : t -> int             one int array, unboxed, no validity array
     note : t -> string option  one string array, and a mask beside it

   [plain] cannot know either of those, so it renders every cell to a boxed
   [string option] and tests every one for absence. On two rows the difference
   is nothing. On a large result set it is the difference between a flat array
   and a few hundred thousand heap allocations, which is the claim. *)

let column (schema : Schema.t) name =
  match Schema.column schema name with
  | Some c -> c
  | None -> failwith (Printf.sprintf "no column %s in %s" name schema.table)

(* The columns the query asks for, in the order it asked. *)
let wanted (schema : Schema.t) (q : Query.t) =
  match q.select with [] -> Schema.names schema | cols -> cols

(* The one place the SQL differs from [Plain.sql]: [select *] is expanded to
   the columns the signature names, rather than sent as a star. Same result
   set, but we know what is coming back and in what order, instead of having
   to discover it from the rows -- which is itself something the .mli bought.
   The predicate is identical, so the database does identical work. *)
let sql (schema : Schema.t) (q : Query.t) =
  Printf.sprintf "SELECT %s FROM %s%s"
    (String.concat ", " (List.map Data.quote (wanted schema q)))
    (Data.quote schema.table)
    (match q.where with
    | None -> ""
    | Some p ->
        Printf.sprintf " WHERE %s %s %s" (Data.quote p.column)
          (Query.op_to_string p.op)
          (Query.value_to_string p.value))

(* Rows in, columns out. [Data.slot] picks the array type and decides whether a
   mask exists, both from the layout alone; [Data.store] fills them and refuses
   a NULL arriving in a column the signature called total. Neither consults a
   value to make a decision, so the shape of the result is fixed before the
   first row is read. *)
let decode (cols : Schema.column list) rows =
  let n = List.length rows in
  let slots = List.map (Data.slot n) cols in
  let pairs = List.combine cols slots in
  List.iteri
    (fun i row -> List.iter2 (fun (c, s) v -> Data.store c s i v) pairs row)
    rows;
  List.map2
    (fun (c : Schema.column) (s : Data.slot) ->
      { Data.name = c.name; values = s.values; valid = s.valid })
    cols slots

(* ---- streaming ---------------------------------------------------------- *)

(* [decode] above waits for [Pg.execute] to build a [Pgx.Value.t list list] --
   200k rows of boxed values, all alive at once -- and only then fills the
   arrays. The rows are consumed once and thrown away, so that list is a
   quarter of a million allocations retained for no reason.

   Streaming skips it: rows arrive one at a time and go straight into typed
   storage. [plain] cannot do this. To write a value into a dense array you
   must know its type before it arrives, and to size the array you must know
   how many are coming; the .mli answers the first, and doubling answers the
   second without the extra counting round trip that would otherwise be
   the price of knowing. *)

type growing = {
  mutable values : Data.values;
  mutable valid : bool array option;
  mutable len : int;
}

let capacity g =
  match g.values with
  | Data.Ints a -> Array.length a
  | Data.Floats a -> Array.length a
  | Data.Texts a -> Array.length a

(* Same mapping as [Data.slot]: the layout picks the array type, and the
   constructor decides whether a mask exists at all. *)
let growing (c : Schema.column) cap =
  let shape, valid =
    match c.layout with
    | Schema.Plain s -> (s, None)
    | Schema.Nullable s -> (s, Some (Array.make cap false))
  in
  let values =
    match shape with
    | Schema.Dense Schema.Int | Schema.Dense Schema.Bool -> Data.Ints (Array.make cap 0)
    | Schema.Dense Schema.Float -> Data.Floats (Array.make cap 0.)
    | Schema.Var -> Data.Texts (Array.make cap "")
  in
  { values; valid; len = 0 }

let grow g =
  let n = max 1024 (2 * capacity g) in
  let blit make a = let b = make n in Array.blit a 0 b 0 g.len; b in
  g.values <-
    (match g.values with
    | Data.Ints a -> Data.Ints (blit (fun n -> Array.make n 0) a)
    | Data.Floats a -> Data.Floats (blit (fun n -> Array.make n 0.) a)
    | Data.Texts a -> Data.Texts (blit (fun n -> Array.make n "") a));
  match g.valid with
  | None -> ()
  | Some v -> g.valid <- Some (blit (fun n -> Array.make n false) v)

let push (c : Schema.column) g v =
  if g.len >= capacity g then grow g;
  let i = g.len in
  let present =
    match g.values with
    | Data.Ints a -> (
        match Pgx.Value.to_int v with Some x -> a.(i) <- x; true | None -> false)
    | Data.Floats a -> (
        match Pgx.Value.to_float v with Some x -> a.(i) <- x; true | None -> false)
    | Data.Texts a -> (
        match Pgx.Value.to_string v with Some x -> a.(i) <- x; true | None -> false)
  in
  (match g.valid with
  | Some valid -> valid.(i) <- present
  | None ->
      if not present then
        failwith
          (Printf.sprintf "%s is NULL in the data, but its signature says otherwise"
             c.name));
  g.len <- i + 1

(* Doubling overshoots, so the arrays are trimmed once at the end. One blit per
   column against a list of every value ever seen. *)
let finish (c : Schema.column) g =
  let take a = Array.sub a 0 g.len in
  { Data.name = c.name;
    values =
      (match g.values with
      | Data.Ints a -> Data.Ints (take a)
      | Data.Floats a -> Data.Floats (take a)
      | Data.Texts a -> Data.Texts (take a));
    valid = Option.map take g.valid }

let stream (cols : Schema.column list) sql =
  let gs = List.map (fun c -> growing c 1024) cols in
  let pairs = List.combine cols gs in
  Data.fetch_iter sql ~f:(fun row -> List.iter2 (fun (c, g) v -> push c g v) pairs row);
  List.map2 finish cols gs

let run_materialised (schema : Schema.t) (q : Query.t) =
  let cols = List.map (column schema) (wanted schema q) in
  decode cols (Data.fetch (sql schema q))

let run (schema : Schema.t) (q : Query.t) =
  stream (List.map (column schema) (wanted schema q)) (sql schema q)

(* ---- querying what was already decoded ----------------------------------- *)

(* The load-once/query-many workload, [tuned]'s half. This is where the arrays
   stop being a nicer shape and start being the point: the text was parsed once,
   at load, and every query after that compares machine values. *)

let find columns name =
  match Data.find columns name with
  | Some c -> c
  | None -> failwith (Printf.sprintf "%s was not loaded" name)

let scan n keep =
  let rec go i acc = if i < 0 then acc else go (i - 1) (if keep i then i :: acc else acc) in
  go (n - 1) []

let guarded_scan (c : Data.t) test = function
  | false -> scan (Data.length c) test
  | true -> (
      match c.valid with
      | Some v -> scan (Data.length c) (fun i -> v.(i) && test i)
      (* Unreachable: [guarded] is true only where the layout was Nullable,
         which is the same word that made the mask exist. *)
      | None -> failwith (Printf.sprintf "%s has no validity array" c.name))

let holds_text op c =
  match op with
  | Query.Eq -> c = 0
  | Query.Ne -> c <> 0
  | Query.Lt -> c < 0
  | Query.Le -> c <= 0
  | Query.Gt -> c > 0
  | Query.Ge -> c >= 0

(* The type match and the operator are lifted out of the loop, because
   [Analysis.plan] resolved both from the .mli before any row was touched. *)
let surviving (columns : Data.t list) (f : Analysis.filter) =
  match f with
  | Analysis.Keep_all ->
      scan (match columns with [] -> 0 | c :: _ -> Data.length c) (fun _ -> true)
  | Analysis.Int_compare { column; op; operand; guarded } -> (
      let c = find columns column in
      match c.values with
      | Data.Ints a ->
          guarded_scan c
            (match op with
            | Query.Eq -> fun i -> Array.unsafe_get a i = operand
            | Query.Ne -> fun i -> Array.unsafe_get a i <> operand
            | Query.Lt -> fun i -> Array.unsafe_get a i < operand
            | Query.Le -> fun i -> Array.unsafe_get a i <= operand
            | Query.Gt -> fun i -> Array.unsafe_get a i > operand
            | Query.Ge -> fun i -> Array.unsafe_get a i >= operand)
            guarded
      | _ -> failwith (Printf.sprintf "%s is not an int column" column))
  | Analysis.Float_compare { column; op; operand; guarded } -> (
      let c = find columns column in
      match c.values with
      | Data.Floats a ->
          guarded_scan c
            (match op with
            | Query.Eq -> fun i -> Array.unsafe_get a i = operand
            | Query.Ne -> fun i -> Array.unsafe_get a i <> operand
            | Query.Lt -> fun i -> Array.unsafe_get a i < operand
            | Query.Le -> fun i -> Array.unsafe_get a i <= operand
            | Query.Gt -> fun i -> Array.unsafe_get a i > operand
            | Query.Ge -> fun i -> Array.unsafe_get a i >= operand)
            guarded
      | _ -> failwith (Printf.sprintf "%s is not a float column" column))
  | Analysis.Text_compare { column; op; operand; guarded } -> (
      let c = find columns column in
      match c.values with
      | Data.Texts a ->
          guarded_scan c
            (fun i -> holds_text op (String.compare (Array.unsafe_get a i) operand))
            guarded
      | _ -> failwith (Printf.sprintf "%s is not a text column" column))

(* Values and mask permuted by the same indices, so absences stay attached to
   the rows they belong to. *)
let gather (c : Data.t) rows =
  let pick f = Array.of_list (List.map f rows) in
  { Data.name = c.name;
    values =
      (match c.values with
      | Data.Ints a -> Data.Ints (pick (fun i -> a.(i)))
      | Data.Floats a -> Data.Floats (pick (fun i -> a.(i)))
      | Data.Texts a -> Data.Texts (pick (fun i -> a.(i))));
    valid = Option.map (fun v -> pick (fun i -> v.(i))) c.valid }

(* [Identity] is the case worth having: no predicate means no rows removed,
   so the answer is the arrays themselves, copied nowhere. *)
let query (schema : Schema.t) (columns : Data.t list) (q : Query.t) =
  let plan = Analysis.plan schema q in
  match plan.project with
  | Analysis.Identity names -> List.map (find columns) names
  | Analysis.Gather names ->
      let rows = surviving columns plan.filter in
      List.map (fun n -> gather (find columns n) rows) names
