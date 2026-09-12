(* The page, on localhost:8000.

   The .mli is re-read on every request. That is the point: edit
   schema/orders.mli, press Run, and watch the analysis change its mind with
   no rebuild and no restart. A signature that has to be recompiled to take
   effect is a much less convincing demonstration than one that does not.

   Today this serves what exists -- the signature, what we parsed it into, and
   what a query parsed to. The kernels are marked as waiting; when plain.ml
   and tuned.ml land, [run_query] gains their results and the page gains a
   table. Nothing else here changes. *)

open Tatami
module S = Tiny_httpd

let schema_path =
  match Sys.getenv_opt "TATAMI_SCHEMA" with
  | Some p -> p
  | None -> "schema/orders.mli"

let page_path =
  match Sys.getenv_opt "TATAMI_WEB" with
  | Some p -> p
  | None -> "web/index.html"

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let json ?(code = 200) j =
  S.Response.make_string
    ~headers:[ ("Content-Type", "application/json") ]
    ~code
    (Ok (Yojson.Safe.to_string j))

let fail code msg = json ~code (`Assoc [ ("error", `String msg) ])

(* ---- the signature ------------------------------------------------------ *)

(* Both the text of the file and what we understood it to mean. Showing the
   two side by side is what makes the parse checkable by eye: if a column is
   missing from the right-hand list, we did not understand its line. *)
let schema_json () =
  let schema = Schema.load schema_path in
  `Assoc
    [ ("path", `String schema_path);
      ("table", `String schema.table);
      ("source", `String (read_file schema_path));
      ( "columns",
        `List
          (List.map
             (fun (c : Schema.column) ->
               `Assoc
                 [ ("name", `String c.name);
                   ("layout", `String (Schema.layout_to_string c.layout));
                   ( "nullable",
                     `Bool
                       (match c.layout with
                       | Schema.Nullable _ -> true
                       | Schema.Plain _ -> false) ) ])
             schema.columns) ) ]

(* ---- a query ------------------------------------------------------------ *)

(* A licence is something the signature permits, or a cost it forces. The
   distinction matters on the page: a reader should be able to see at a glance
   which lines are the analysis buying something and which are it conceding
   that it cannot. *)
let licence ?(good = true) text = `Assoc [ ("text", `String text); ("good", `Bool good) ]

let nullable (c : Schema.column) =
  match c.layout with Schema.Nullable _ -> true | Schema.Plain _ -> false

let scalar_note (c : Schema.column) =
  match c.layout with
  | Schema.Plain (Schema.Dense Schema.Int) | Schema.Nullable (Schema.Dense Schema.Int)
    -> Some (licence "dense int: comparison is a machine instruction, values are unboxed")
  | Schema.Plain (Schema.Dense Schema.Float)
  | Schema.Nullable (Schema.Dense Schema.Float) ->
      Some (licence "dense float: unboxed, fixed stride")
  | Schema.Plain (Schema.Dense Schema.Bool) | Schema.Nullable (Schema.Dense Schema.Bool)
    -> Some (licence "dense bool: one byte-wide array")
  | Schema.Plain Schema.Var | Schema.Nullable Schema.Var ->
      Some (licence ~good:false "variable width: an offsets lookup before any comparison")

let stage kernel detail licences =
  `Assoc
    [ ("kernel", `String kernel);
      ("detail", `String detail);
      ("licences", `List licences) ]

let columns_of (schema : Schema.t) (q : Query.t) =
  match q.select with [] -> Schema.names schema | cols -> cols

let lookup (schema : Schema.t) name =
  match Schema.column schema name with
  | Some c -> c
  | None ->
      failwith (Printf.sprintf "no column %s in %s" name schema.table)

(* The scan: which columns are read, and which of them carry a validity array.
   An array that is not allocated is the clearest form the claim takes -- it
   is not a check that is skipped, it is memory that does not exist. *)
let scan_stage schema q =
  let names =
    List.sort_uniq compare
      (columns_of schema q
      @ match q.where with None -> [] | Some p -> [ p.column ])
  in
  let cols = List.map (lookup schema) names in
  let nulls = List.filter nullable cols in
  stage "scan"
    (String.concat ", " names)
    (List.filter_map scalar_note cols
    @
    match nulls with
    | [] -> [ licence "no column here can be null, so no validity array is allocated" ]
    | ns ->
        [ licence ~good:false
            (Printf.sprintf "%s may be null, so a validity array is allocated for %s"
               (String.concat ", " (List.map (fun (c : Schema.column) -> c.name) ns))
               (if List.length ns = 1 then "it" else "each")) ])

let filter_stage schema (q : Query.t) =
  match q.where with
  | None -> None
  | Some p ->
      let c = lookup schema p.column in
      Some
        (stage "filter"
           (Query.predicate_to_string p)
           ((if nullable c then
               [ licence ~good:false
                   "the column may be null, so the loop tests validity on every row" ]
             else
               [ licence "not an option, so no validity test is emitted in the loop" ])
           @ Option.to_list (scalar_note c)))

(* The projection. With no predicate the selection is the identity, so there
   is nothing to gather -- the output columns are the input arrays themselves.
   That is a larger win than anything the predicate offers, and it is invisible
   unless the projection is analysed in its own right. *)
let project_stage schema (q : Query.t) =
  let names = columns_of schema q in
  let cols = List.map (lookup schema) names in
  let any_null = List.exists nullable cols in
  stage "project"
    (String.concat ", " names)
    ((match q.where with
     | None ->
         [ licence
             "no rows are removed, so the projection is the identity: the output \
              columns are the input arrays, copied nowhere" ]
     | Some _ -> [ licence ~good:false "rows were removed, so surviving values are gathered" ])
    @
    if any_null then
      [ licence ~good:false "a validity array is carried through to the output" ]
    else [ licence "no validity array is carried through" ])

let run_query sql =
  try
    let schema = Schema.load schema_path in
    let q = Parser.parse sql in
    if q.table <> schema.table then
      fail 400
        (Printf.sprintf "no table %s; this schema describes %s" q.table schema.table)
    else
      json
        (`Assoc
          [ ("sql", `String sql);
            ("understood", `String (Query.to_string q));
            ("table", `String q.table);
            ( "stages",
              `List
                (scan_stage schema q
                :: (Option.to_list (filter_stage schema q)
                   @ [ project_stage schema q ])) );
            (* Waiting on plain.ml and tuned.ml. When they exist this becomes
               two timings and a table of rows. *)
            ("kernels", `Null) ])
  with
  | Parser.Error m -> fail 400 m
  | Lexer.Error m -> fail 400 m
  | Failure m -> fail 400 m
  | Sys_error m -> fail 500 m
  | e -> fail 500 (Printexc.to_string e)

(* ---- routes ------------------------------------------------------------- *)

let () =
  let port =
    match Sys.getenv_opt "TATAMI_PORT" with
    | Some p -> int_of_string p
    | None -> 8000
  in
  let server = S.create ~port () in

  S.add_route_handler ~meth:`GET server
    S.Route.return
    (fun _ ->
      S.Response.make_string
        ~headers:[ ("Content-Type", "text/html; charset=utf-8") ]
        (Ok (read_file page_path)));

  S.add_route_handler ~meth:`GET server
    S.Route.(exact "api" @/ exact "schema" @/ return)
    (fun _ ->
      try json (schema_json ()) with
      | Sys_error m -> fail 500 m
      | e -> fail 500 (Printexc.to_string e));

  S.add_route_handler ~meth:`POST server
    S.Route.(exact "api" @/ exact "query" @/ return)
    (fun req -> run_query (String.trim (S.Request.body req)));

  Printf.printf "tatami: http://localhost:%d  (schema: %s)\n%!" port schema_path;
  S.run_exn server
