(* The demonstration, on localhost:8000.

     /              the query page: signature in, plan out
     /performance/  what the .mli costs and what it buys, measured live
     /trace/        the same query walked from text to arrays, stage by stage

   The .mli is re-read on every request. That is the point: edit
   schema/orders.mli, press Run, and watch the analysis change its mind with no
   rebuild and no restart. A signature that has to be recompiled to take effect
   is a much less convincing demonstration than one that does not. *)

open Tatami
module S = Tiny_httpd

let schema_path =
  match Sys.getenv_opt "TATAMI_SCHEMA" with Some p -> p | None -> "schema/orders.mli"

let web_dir = match Sys.getenv_opt "TATAMI_WEB" with Some p -> p | None -> "web"
let data_dir = "docs/phase_3/data"

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
let page path =
  S.Response.make_string
    ~headers:[ ("Content-Type", "text/html; charset=utf-8") ]
    (Ok (read_file (Filename.concat web_dir path)))

(* Every route that takes a query runs the same gauntlet, and errors are
   classified by who rejected the query rather than lumped into one code. A
   query the signature cannot describe is the client's mistake, not ours. *)
let with_query f body =
  try f (Parser.parse (String.trim body)) with
  | Parser.Error m -> fail 400 ("parse: " ^ m)
  | Lexer.Error m -> fail 400 ("lex: " ^ m)
  | Analysis.Error m -> fail 400 ("analysis: " ^ m)
  | Failure m -> fail 400 m
  | Sys_error m -> fail 500 m
  | e -> fail 500 (Printexc.to_string e)

(* ---- the signature ------------------------------------------------------ *)

let layout_json (c : Schema.column) =
  `Assoc
    [ ("name", `String c.name);
      ("layout", `String (Schema.layout_to_string c.layout));
      ( "nullable",
        `Bool (match c.layout with Schema.Nullable _ -> true | Schema.Plain _ -> false) );
      ( "dense",
        `Bool
          (match c.layout with
          | Schema.Plain (Schema.Dense _) | Schema.Nullable (Schema.Dense _) -> true
          | _ -> false) ) ]

(* Both the text of the file and what we understood it to mean. Showing the two
   side by side is what makes the parse checkable by eye: if a column is missing
   from the right-hand list, we did not understand its line. *)
let schema_json () =
  let schema = Schema.load schema_path in
  `Assoc
    [ ("path", `String schema_path);
      ("table", `String schema.table);
      ("source", `String (read_file schema_path));
      ("columns", `List (List.map layout_json schema.columns)) ]

(* ---- the plan ----------------------------------------------------------- *)

(* Read from [Analysis] rather than recomputed here. The page and the kernels
   must not be able to drift: if the plan says the loop is unguarded, that is
   the same value the loop was built from. *)
let plan_json (plan : Analysis.t) =
  let guarded = function
    | Analysis.Keep_all -> false
    | Analysis.Int_compare { guarded; _ }
    | Analysis.Float_compare { guarded; _ }
    | Analysis.Text_compare { guarded; _ } -> guarded
  in
  `Assoc
    [ ("read", `List (List.map (fun s -> `String s) plan.read));
      ("filter", `String (Analysis.filter_to_string plan.filter));
      ("guarded", `Bool (guarded plan.filter));
      ( "project",
        `String
          (match plan.project with Analysis.Identity _ -> "identity" | _ -> "gather") );
      ( "projected",
        `List
          (List.map
             (fun s -> `String s)
             (match plan.project with Analysis.Identity n | Analysis.Gather n -> n)) );
      ("summary", `String (Analysis.to_string plan)) ]

(* A licence is something the signature permits; a cost is one it could not
   remove. Keeping them apart on the page is what lets a reader tell at a glance
   which lines are the analysis buying something and which are it conceding. *)
let licence ?(good = true) text = `Assoc [ ("text", `String text); ("good", `Bool good) ]

let licences (schema : Schema.t) (plan : Analysis.t) =
  let col n = Schema.column schema n in
  let of_column n =
    match col n with
    | None -> []
    | Some c -> (
        let nullable =
          match c.layout with Schema.Nullable _ -> true | Schema.Plain _ -> false
        in
        (match c.layout with
        | Schema.Plain (Schema.Dense Schema.Int) | Schema.Nullable (Schema.Dense Schema.Int)
          -> [ licence (n ^ ": dense int, comparison is a machine instruction") ]
        | Schema.Plain (Schema.Dense Schema.Float)
        | Schema.Nullable (Schema.Dense Schema.Float) ->
            [ licence (n ^ ": dense float, unboxed and fixed stride");
              licence ~good:false (n ^ ": text must be parsed to float once, at load") ]
        | Schema.Plain (Schema.Dense Schema.Bool) | Schema.Nullable (Schema.Dense Schema.Bool)
          -> [ licence (n ^ ": dense bool, one byte-wide array") ]
        | Schema.Plain Schema.Var | Schema.Nullable Schema.Var ->
            [ licence ~good:false (n ^ ": variable width, and no parse to hoist") ])
        @
        if nullable then
          [ licence ~good:false (n ^ ": may be null, so a validity array is allocated") ]
        else [ licence (n ^ ": cannot be null, so no validity array exists") ])
  in
  List.concat_map of_column plan.read

let plan_route body =
  with_query
    (fun q ->
      let schema = Schema.load schema_path in
      let plan = Analysis.plan schema q in
      json
        (`Assoc
          [ ("sql", `String (Query.to_string q));
            ("table", `String q.table);
            ("plan", plan_json plan);
            ("licences", `List (licences schema plan)) ]))
    body

(* ---- the trace ---------------------------------------------------------- *)

(* Purely expository: every stage the query passes through, in order, with what
   it looked like on the way in and on the way out. Nothing here is needed to
   answer a query -- it exists so the pipeline can be read rather than trusted. *)

let token_json t =
  let kind, text =
    match t with
    | Lexer.Word w -> ("word", w)
    | Lexer.Num n -> ("num", n)
    | Lexer.Str s -> ("str", s)
    | Lexer.Punct p -> ("punct", p)
    | Lexer.End -> ("end", "")
  in
  `Assoc [ ("kind", `String kind); ("text", `String text) ]

let value_json = function
  | Query.Int n -> `Assoc [ ("ctor", `String "Int"); ("text", `String (string_of_int n)) ]
  | Query.Float f ->
      `Assoc [ ("ctor", `String "Float"); ("text", `String (Printf.sprintf "%g" f)) ]
  | Query.Text s -> `Assoc [ ("ctor", `String "Text"); ("text", `String s) ]

let column_json (c : Data.t) =
  let kind, sample =
    match c.values with
    | Data.Ints a -> ("int array", Array.length a)
    | Data.Floats a -> ("float array", Array.length a)
    | Data.Texts a -> ("string array", Array.length a)
  in
  `Assoc
    [ ("name", `String c.name);
      ("storage", `String kind);
      ("length", `Int sample);
      ("mask", `Bool (c.valid <> None));
      ( "nulls",
        `Int
          (match c.valid with
          | None -> 0
          | Some v -> Array.fold_left (fun a b -> if b then a else a + 1) 0 v) ) ]

let preview cols n =
  let len = match cols with [] -> 0 | c :: _ -> Data.length c in
  let take = min n len in
  `List
    (List.init take (fun i ->
         `List
           (List.map
              (fun c -> match Data.cell c i with None -> `Null | Some s -> `String s)
              cols)))

let trace_route body =
  with_query
    (fun q ->
      let text = String.trim body in
      let schema = Schema.load schema_path in
      let plan = Analysis.plan schema q in
      let tuned_sql = Tuned.sql schema q in
      let cols = Tuned.run schema q in
      let plain_rows = Plain.run q in
      json
        (`Assoc
          [ ("text", `String text);
            ("tokens", `List (List.map token_json (Lexer.tokenise text)));
            ( "query",
              `Assoc
                [ ("table", `String q.table);
                  ("select", `List (List.map (fun s -> `String s) q.select));
                  ( "where",
                    match q.where with
                    | None -> `Null
                    | Some p ->
                        `Assoc
                          [ ("column", `String p.column);
                            ("op", `String (Query.op_to_string p.op));
                            ("value", value_json p.value) ] ) ] );
            ("schema", schema_json ());
            ("plan", plan_json plan);
            ("licences", `List (licences schema plan));
            ("plain_sql", `String (Plain.sql q));
            ("tuned_sql", `String tuned_sql);
            ("plain_rows", `Int (List.length plain_rows));
            ("columns", `List (List.map column_json cols));
            ("preview", preview cols 10) ]))
    body

(* ---- performance -------------------------------------------------------- *)

let phase_json (p : Run.phase) =
  `Assoc [ ("name", `String p.name); ("ms", `Float (p.seconds *. 1000.)) ]

let outcome_json (o : Run.outcome) =
  `Assoc
    [ ("kernel", `String o.kernel);
      ("sql", `String o.sql);
      ("ms", `Float (o.seconds *. 1000.));
      ("kwords", `Float (o.words /. 1000.));
      ("rows", `Int (List.length o.rows));
      ("phases", `List (List.map phase_json o.phases)) ]

let measure_route body =
  with_query
    (fun q ->
      let schema = Schema.load schema_path in
      let r = Run.median ~n:5 schema q in
      json
        (`Assoc
          [ ("sql", `String (Query.to_string q));
            ("agree", `Bool r.agree);
            ("plain", outcome_json r.plain);
            ("tuned", outcome_json r.tuned) ]))
    body

(* The frozen figures from `dune exec bin/bench.exe`, served as they were
   written. A live run on a laptop with a browser open is not the number to
   put in a paper; these are, and the page says which is which. *)
let dat name =
  let rows =
    read_file (Filename.concat data_dir name)
    |> String.split_on_char '\n'
    |> List.filter (fun l -> String.trim l <> "")
    |> List.map (fun l ->
           `List
             (String.split_on_char ' ' l
             |> List.filter (fun s -> s <> "")
             |> List.map (fun s -> `String s)))
  in
  `List rows

let bench_route () =
  try
    json
      (`Assoc
        [ ("materialise", dat "materialise.dat");
          ("columns", dat "columns.dat");
          ("workload", dat "workload.dat");
          ("rounds", dat "rounds.dat") ])
  with Sys_error _ ->
    fail 404 "no frozen measurements; run: dune exec bin/bench.exe"

(* ---- routes ------------------------------------------------------------- *)

let () =
  let port =
    match Sys.getenv_opt "TATAMI_PORT" with Some p -> int_of_string p | None -> 8000
  in
  let server = S.create ~port () in
  let get path handler = S.add_route_handler ~meth:`GET server path handler in
  let post path handler = S.add_route_handler ~meth:`POST server path handler in

  get S.Route.return (fun _ -> page "index.html");
  get S.Route.(exact "performance" @/ return) (fun _ -> page "performance.html");
  get S.Route.(exact "trace" @/ return) (fun _ -> page "trace.html");

  get S.Route.(exact "api" @/ exact "schema" @/ return) (fun _ ->
      try json (schema_json ()) with
      | Sys_error m -> fail 500 m
      | e -> fail 500 (Printexc.to_string e));
  get S.Route.(exact "api" @/ exact "bench" @/ return) (fun _ -> bench_route ());
  post S.Route.(exact "api" @/ exact "query" @/ return) (fun req ->
      plan_route (S.Request.body req));
  post S.Route.(exact "api" @/ exact "trace" @/ return) (fun req ->
      trace_route (S.Request.body req));
  post S.Route.(exact "api" @/ exact "measure" @/ return) (fun req ->
      measure_route (S.Request.body req));

  Printf.printf "tatami: http://localhost:%d  (schema: %s)\n" port schema_path;
  Printf.printf "        http://localhost:%d/performance/\n" port;
  Printf.printf "        http://localhost:%d/trace/\n%!" port;
  S.run_exn server
