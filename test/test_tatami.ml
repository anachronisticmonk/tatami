(* Unit tests for the pieces that read an .mli.

   These are all pure functions over strings, and they carry more risk than
   they look like they do: if a layout is parsed wrongly, the analysis picks
   the wrong loop and [tuned] returns wrong answers quietly. It is the one bug
   here that would not announce itself. *)

open Tatami

(* ---- parse_line --------------------------------------------------------- *)

(* Failures print the .mli line rather than a constructor dump. *)
let show = function
  | None -> "-"
  | Some (c : Schema.column) -> c.name ^ " : " ^ Schema.layout_to_string c.layout

let parses line expected () =
  Alcotest.(check string) line expected (show (Schema.parse_line line))

let parse_line_cases =
  [ ("int", "val qty : t -> int", "qty : int");
    ("float", "val price : t -> float", "price : float");
    ("bool", "val paid : t -> bool", "paid : bool");
    ("string", "val sku : t -> string", "sku : string");
    ("generated key", "val id : t -> id", "id : int");
    ("optional int", "val n : t -> int option", "n : int option");
    ("optional string", "val note : t -> string option", "note : string option");
    ("alignment padding", "val qty    :   t -> int", "qty : int");
    ("leading space", "  val qty : t -> int", "qty : int");
    (* everything below is correctly not a column *)
    ("abstract type", "type t", "-");
    ("blank line", "", "-");
    ("not an accessor on t", "val all : db -> t list", "-");
    ("type we do not know", "val placed : t -> date", "-");
    ("no arrow at all", "val x : t", "-");
    (* A known limit, recorded rather than fixed: whitespace squeezing was
       dropped, so two spaces after [val] is not recognised. Phase 1 will not
       emit that. If it ever does, this test turns red and says why. *)
    ("two spaces after val", "val  qty : t -> int", "-") ]

let parse_line_tests =
  List.map
    (fun (name, line, expected) ->
      Alcotest.test_case name `Quick (parses line expected))
    parse_line_cases

(* ---- split_arrow -------------------------------------------------------- *)

let arrow = Alcotest.(option (pair string string))

let splits input expected () =
  Alcotest.check arrow input expected (Schema.split_arrow input)

let split_arrow_cases =
  [ ("simple", "t -> int", Some ("t", "int"));
    ("two words on the right", "t -> string option", Some ("t", "string option"));
    ("no spaces", "t->int", Some ("t", "int"));
    ("not an accessor on t", "db -> t list", Some ("db", "t list"));
    ("no arrow", "t", None);
    ("empty", "", None);
    (* Only the first arrow is used. A curried accessor would split here into
       ("t", "int -> bool"), which [layout_of_type] then rejects -- so a
       two-argument accessor is dropped rather than misread. *)
    ("two arrows", "t -> int -> bool", Some ("t", "int -> bool")) ]

let split_arrow_tests =
  List.map
    (fun (name, input, expected) ->
      Alcotest.test_case name `Quick (splits input expected))
    split_arrow_cases

(* ---- layout_of_type ----------------------------------------------------- *)

let renders input expected () =
  let got =
    match Schema.layout_of_type input with
    | None -> "-"
    | Some l -> Schema.layout_to_string l
  in
  Alcotest.(check string) input expected got

(* Every accepted type renders back to the syntax it was written in. If these
   two ever disagree, one of them is wrong and the .mli shown on the page
   would not be the .mli we understood. *)
let layout_cases =
  [ "int"; "float"; "bool"; "string"; "int option"; "float option";
    "bool option"; "string option" ]

let layout_of_type_tests =
  List.map
    (fun ty -> Alcotest.test_case ("round trip: " ^ ty) `Quick (renders ty ty))
    layout_cases
  @ [ Alcotest.test_case "id becomes int" `Quick (renders "id" "int");
      Alcotest.test_case "unknown" `Quick (renders "date" "-");
      Alcotest.test_case "not a type" `Quick (renders "" "-") ]

(* ---- lookups ------------------------------------------------------------ *)

let orders : Schema.t =
  { table = "orders";
    columns =
      [ { name = "id"; layout = Schema.Plain (Schema.Dense Schema.Int) };
        { name = "qty"; layout = Schema.Plain (Schema.Dense Schema.Int) };
        { name = "note"; layout = Schema.Nullable Schema.Var } ] }

let lookup_tests =
  [ Alcotest.test_case "column found" `Quick (fun () ->
        Alcotest.(check string)
          "qty" "int"
          (match Schema.column orders "qty" with
          | Some c -> Schema.layout_to_string c.layout
          | None -> "-"));
    Alcotest.test_case "column absent" `Quick (fun () ->
        Alcotest.(check bool)
          "no such column" true
          (Schema.column orders "nope" = None));
    Alcotest.test_case "names" `Quick (fun () ->
        Alcotest.(check (list string))
          "in order" [ "id"; "qty"; "note" ] (Schema.names orders)) ]

(* ---- read_file ---------------------------------------------------------- *)

(* The only function here that touches the filesystem, so the only one that
   needs a file to test it. Written and removed within the test, so nothing
   outside the sandbox is involved. *)
let read_file_tests =
  [ Alcotest.test_case "reads a whole file" `Quick (fun () ->
        let path = Filename.temp_file "tatami" ".mli" in
        let body = "type t\nval qty : t -> int\n" in
        let oc = open_out_bin path in
        output_string oc body;
        close_out oc;
        let got = Schema.read_file path in
        Sys.remove path;
        Alcotest.(check string) "contents" body got);
    Alcotest.test_case "reads an empty file" `Quick (fun () ->
        let path = Filename.temp_file "tatami" ".mli" in
        let got = Schema.read_file path in
        Sys.remove path;
        Alcotest.(check string) "empty" "" got) ]

(* ---- load --------------------------------------------------------------- *)

let write_mli body =
  let path = Filename.temp_file "orders" ".mli" in
  let oc = open_out_bin path in
  output_string oc body;
  close_out oc;
  path

let loads body expected () =
  let path = write_mli body in
  let s = Schema.load path in
  Sys.remove path;
  let rendered =
    List.map
      (fun (c : Schema.column) ->
        c.name ^ " : " ^ Schema.layout_to_string c.layout)
      s.columns
  in
  Alcotest.(check (list string)) body expected rendered

let load_cases =
  [ ( "a whole signature",
      "type t\n\
       type id\n\
       \n\
       val id    : t -> id\n\
       val qty   : t -> int\n\
       val note  : t -> string option\n",
      [ "id : int"; "qty : int"; "note : string option" ] );
    ("only declarations", "type t\ntype id\n", []);
    ("empty file", "", []);
    (* Order is preserved, because the position of a column in the file is
       the position it will have in the data. *)
    ( "order is kept",
      "val b : t -> int\nval a : t -> int\n",
      [ "b : int"; "a : int" ] );
    (* Lines we cannot read are dropped, not guessed at. A wrong layout would
       make [tuned] run the wrong loop and answer wrongly in silence. *)
    ( "unreadable lines are dropped",
      "val qty : t -> int\nval placed : t -> date\nval all : db -> t list\n",
      [ "qty : int" ] ) ]

let load_tests =
  List.map
    (fun (name, body, expected) ->
      Alcotest.test_case name `Quick (loads body expected))
    load_cases
  @ [ Alcotest.test_case "table name comes from the filename" `Quick (fun () ->
          let path = Filename.concat (Filename.get_temp_dir_name ()) "widgets.mli" in
          let oc = open_out_bin path in
          output_string oc "val n : t -> int\n";
          close_out oc;
          let s = Schema.load path in
          Sys.remove path;
          Alcotest.(check string) "table" "widgets" s.table);
      (* The file the program actually reads. If Phase 1's shape drifts from
         what we parse, this is where it shows up first. *)
      (* The files the program actually reads. If Phase 1's shape drifts from
         what we parse, this is where it shows up first. *)
      Alcotest.test_case "the real schema/step.mli" `Quick (fun () ->
          let s = Schema.load "../schema/step.mli" in
          Alcotest.(check string) "table" "step" s.table;
          Alcotest.(check (list string))
            "columns"
            [ "id"; "job_id"; "idx"; "name"; "ms"; "rate"; "error" ]
            (Schema.names s));
      (* A foreign key is a dense int that remembers where it points. *)
      Alcotest.test_case "a cross-module key is read as a key" `Quick (fun () ->
          let s = Schema.load "../schema/step.mli" in
          match Schema.column s "job_id" with
          | Some c ->
              Alcotest.(check string) "prints as" "Job.id"
                (Schema.layout_to_string c.layout);
              Alcotest.(check (option string)) "points at" (Some "job") (Schema.target c)
          | None -> Alcotest.fail "job_id missing");
      (* Seven .mli files, seven tables, and the whole corpus is reachable
         from repository by following keys. *)
      Alcotest.test_case "the whole schema directory" `Quick (fun () ->
          let db = Schema.load_dir "../schema" in
          Alcotest.(check (list string))
            "tables"
            [ "job"; "repo"; "run"; "step" ]
            (List.map (fun (t : Schema.t) -> t.table) db);
          let keys =
            List.concat_map
              (fun (t : Schema.t) ->
                List.filter_map
                  (fun c -> Option.map (fun d -> t.table ^ "->" ^ d) (Schema.target c))
                  t.columns)
              db
          in
          Alcotest.(check (list string))
            "references"
            [ "job->run"; "run->repo"; "step->job" ]
            keys) ]

(* ---- query printing ----------------------------------------------------- *)

(* [to_string] is what the page will show, so it has to be the query we
   understood rather than the text that was typed. Once the parser exists,
   these same strings become round-trip tests: parse then print should be the
   identity on everything we accept. *)
let prints q expected () =
  Alcotest.(check string) expected expected (Query.to_string q)

let q ?where ?(select = []) table : Query.t = { table; select; where }

let query_cases =
  [ ( "the query we are building for",
      q "orders" ~select:[ "qty" ]
        ~where:{ column = "qty"; op = Query.Gt; value = Query.Int 4 },
      "select qty from orders where qty > 4" );
    ("no predicate", q "orders" ~select:[ "qty" ], "select qty from orders");
    ( "several columns",
      q "orders" ~select:[ "id"; "qty"; "sku" ],
      "select id, qty, sku from orders" );
    ("empty select is a star", q "orders", "select * from orders");
    ( "a string literal is quoted",
      q "orders" ~select:[ "sku" ]
        ~where:{ column = "sku"; op = Query.Eq; value = Query.Text "TATAMI-01" },
      "select sku from orders where sku = 'TATAMI-01'" );
    ( "a float literal",
      q "orders" ~select:[ "price" ]
        ~where:{ column = "price"; op = Query.Le; value = Query.Float 49.5 },
      "select price from orders where price <= 49.5" ) ]

let query_tests =
  List.map
    (fun (name, query, expected) ->
      Alcotest.test_case name `Quick (prints query expected))
    query_cases

let op_tests =
  [ Alcotest.test_case "every operator prints" `Quick (fun () ->
        Alcotest.(check (list string))
          "operators"
          [ "="; "<>"; "<"; "<="; ">"; ">=" ]
          (List.map Query.op_to_string
             [ Query.Eq; Query.Ne; Query.Lt; Query.Le; Query.Gt; Query.Ge ])) ]

(* ---- lexer -------------------------------------------------------------- *)

let tokens s = String.concat " " (List.map Lexer.to_string (Lexer.tokenise s))

let lexes input expected () =
  Alcotest.(check string) input expected (tokens input)

(* [to_string] renders a token back to the text it came from, so the expected
   column reads as the query does -- except that [End] is always there, and
   words have been folded to lower case. *)
let lexer_cases =
  [ ("select star", "select * from orders", "select * from orders end of query");
    ( "the query we are building for",
      "select qty from orders where qty > 4",
      "select qty from orders where qty > 4 end of query" );
    ("keywords are folded", "SELECT QTY FROM Orders", "select qty from orders end of query");
    ("a column list", "select id, qty from orders", "select id , qty from orders end of query");
    ("nothing at all", "", "end of query");
    ("just whitespace", "   \n\t ", "end of query");
    (* literals are not folded: they are data, not names *)
    ("a string literal", "where sku = 'TATAMI-01'", "where sku = 'TATAMI-01' end of query");
    ("an escaped quote", "where s = 'it''s'", "where s = 'it's' end of query");
    (* two-character operators win over their first character *)
    ("less or equal", "qty <= 4", "qty <= 4 end of query");
    ("not equal", "qty <> 4", "qty <> 4 end of query");
    ("bang equals is normalised", "qty != 4", "qty <> 4 end of query");
    ("plain less than", "qty < 4", "qty < 4 end of query");
    (* numbers keep their text so the parser can decide int or float *)
    ("an integer", "4", "4 end of query");
    ("a float", "4.5", "4.5 end of query");
    ("a negative", "-4", "-4 end of query");
    ("no space needed", "qty>4", "qty > 4 end of query") ]

let lexer_tests =
  List.map
    (fun (name, input, expected) ->
      Alcotest.test_case name `Quick (lexes input expected))
    lexer_cases

let raises what f () =
  Alcotest.(check bool)
    what true
    (try
       ignore (f ());
       false
     with Lexer.Error _ -> true)

let lexer_error_tests =
  [ Alcotest.test_case "unterminated literal" `Quick
      (raises "unterminated" (fun () -> Lexer.tokenise "where s = 'oops"));
    Alcotest.test_case "illegal character" `Quick
      (raises "illegal" (fun () -> Lexer.tokenise "select # from orders")) ]

(* ---- parser ------------------------------------------------------------- *)

let contains haystack needle =
  let n = String.length needle and h = String.length haystack in
  let rec go i = i + n <= h && (String.sub haystack i n = needle || go (i + 1)) in
  n = 0 || go 0

(* Parsing then printing should be the identity on everything we accept. That
   is a stronger check than asserting on constructors: a parser that silently
   drops a clause loses it from the output, and this notices. *)
let round_trips input () =
  Alcotest.(check string) input input (Query.to_string (Parser.parse input))

let parses_as input expected () =
  Alcotest.(check string) input expected (Query.to_string (Parser.parse input))

let round_trip_cases =
  [ "select * from orders";
    "select qty from orders";
    "select id, qty, sku from orders";
    "select qty from orders where qty > 4";
    "select * from orders where qty >= 2";
    "select sku from orders where sku = 'TATAMI-01'";
    "select price from orders where price <= 49.5";
    "select qty from orders where qty <> 0";
    "select qty from orders where qty < 100";
    "select note from orders where note = 'rush'" ]

let parser_tests =
  List.map
    (fun q -> Alcotest.test_case q `Quick (round_trips q))
    round_trip_cases
  @ [ (* the surface is forgiving; the value it produces is canonical *)
      Alcotest.test_case "keywords are case insensitive" `Quick
        (parses_as "SELECT QTY FROM Orders WHERE Qty > 4"
           "select qty from orders where qty > 4");
      Alcotest.test_case "whitespace is irrelevant" `Quick
        (parses_as "select\n  qty\nfrom orders\nwhere qty>4"
           "select qty from orders where qty > 4");
      Alcotest.test_case "bang equals becomes <>" `Quick
        (parses_as "select qty from orders where qty != 4"
           "select qty from orders where qty <> 4");
      Alcotest.test_case "an escaped quote survives" `Quick
        (parses_as "select sku from orders where sku = \'it\'\'s\'"
           "select sku from orders where sku = \'it\'s\'");
      (* a whole number is an int, a dotted one is a float *)
      Alcotest.test_case "4 is an int" `Quick (fun () ->
          match (Parser.parse "select qty from orders where qty > 4").where with
          | Some { value = Query.Int 4; _ } -> ()
          | _ -> Alcotest.fail "expected Int 4");
      Alcotest.test_case "4.0 is a float" `Quick (fun () ->
          match (Parser.parse "select qty from orders where qty > 4.0").where with
          | Some { value = Query.Float 4.0; _ } -> ()
          | _ -> Alcotest.fail "expected Float 4.");
      Alcotest.test_case "a negative literal" `Quick (fun () ->
          match (Parser.parse "select qty from orders where qty > -4").where with
          | Some { value = Query.Int (-4); _ } -> ()
          | _ -> Alcotest.fail "expected Int (-4)");
      Alcotest.test_case "star is an empty select list" `Quick (fun () ->
          Alcotest.(check (list string))
            "empty" [] (Parser.parse "select * from orders").select) ]

(* Every failure says what it expected and what it found. A parser that only
   says "syntax error" is a parser nobody can use. *)
let fails input fragment () =
  match Parser.parse input with
  | exception Parser.Error m ->
      Alcotest.(check bool)
        (Printf.sprintf "%s  ->  %s" input m)
        true (contains m fragment)
  | exception Lexer.Error m ->
      Alcotest.(check bool)
        (Printf.sprintf "%s  ->  %s" input m)
        true (contains m fragment)
  | _ -> Alcotest.fail (input ^ " should not have parsed")

let parser_error_cases =
  [ ("empty query", "", "expected select");
    ("does not start with select", "from orders", "expected select");
    ("no from", "select qty orders", "expected from");
    ("no table", "select qty from", "expected a name");
    ("no column after a comma", "select id, from orders", "expected from");
    ("not a comparison", "select qty from orders where qty like 4", "expected a comparison");
    ("no value", "select qty from orders where qty >", "expected a value");
    ("a column on the right", "select qty from orders where qty > price", "expected a value");
    ("trailing rubbish", "select qty from orders rubbish", "unexpected");
    ("a second predicate", "select qty from orders where a > 1 and b > 2", "unexpected");
    ("unterminated literal", "select sku from orders where sku = \'oops", "unterminated");
    ("illegal character", "select # from orders", "unexpected character") ]

let parser_error_tests =
  List.map
    (fun (name, input, fragment) ->
      Alcotest.test_case name `Quick (fails input fragment))
    parser_error_cases

(* The helpers are reachable with an empty token list only by calling them
   directly -- the lexer always appends [End]. Covered here so that the
   "found nothing" branches are not dead code nobody has ever run. *)
let raises_parser what f () =
  Alcotest.(check bool)
    what true
    (try
       ignore (f ());
       false
     with Parser.Error _ -> true)

let parser_helper_tests =
  [ Alcotest.test_case "keyword on nothing" `Quick
      (raises_parser "keyword" (fun () -> Parser.keyword "select" []));
    Alcotest.test_case "name on nothing" `Quick
      (raises_parser "name" (fun () -> Parser.name []));
    Alcotest.test_case "comparison on nothing" `Quick
      (raises_parser "comparison" (fun () -> Parser.comparison []));
    Alcotest.test_case "literal on nothing" `Quick
      (raises_parser "literal" (fun () -> Parser.literal []));
    Alcotest.test_case "every comparison operator" `Quick (fun () ->
        let ops =
          [ "="; "<>"; "<"; "<="; ">"; ">=" ]
          |> List.map (fun o ->
                 let q = Parser.parse ("select qty from orders where qty " ^ o ^ " 1") in
                 match q.where with
                 | Some p -> Query.op_to_string p.op
                 | None -> "-")
        in
        Alcotest.(check (list string))
          "all six" [ "="; "<>"; "<"; "<="; ">"; ">=" ] ops) ]

(* ---- data --------------------------------------------------------------- *)

(* A column that promised it cannot be null carries no validity array at all,
   which is the representational half of the thesis: the .mli does not merely
   describe the data, it decides its shape in memory. *)
let qty : Data.t =
  { name = "qty"; values = Data.Ints [| 1; 5; 3 |]; valid = None }

let note : Data.t =
  { name = "note";
    values = Data.Texts [| "rush"; ""; "gift" |];
    valid = Some [| true; false; true |] }

let price : Data.t =
  { name = "price"; values = Data.Floats [| 49.5; 18.0; 240.0 |]; valid = None }

let data_tests =
  [ Alcotest.test_case "length of an int column" `Quick (fun () ->
        Alcotest.(check int) "three" 3 (Data.length qty));
    Alcotest.test_case "length of a text column" `Quick (fun () ->
        Alcotest.(check int) "three" 3 (Data.length note));
    Alcotest.test_case "length of a float column" `Quick (fun () ->
        Alcotest.(check int) "three" 3 (Data.length price));
    (* no validity array means every row is present, and nothing is read *)
    Alcotest.test_case "a plain column is valid everywhere" `Quick (fun () ->
        Alcotest.(check (list bool))
          "all present" [ true; true; true ]
          (List.init 3 (Data.is_valid qty)));
    Alcotest.test_case "a nullable column reads its array" `Quick (fun () ->
        Alcotest.(check (list bool))
          "middle is absent" [ true; false; true ]
          (List.init 3 (Data.is_valid note)));
    Alcotest.test_case "cells of an int column" `Quick (fun () ->
        Alcotest.(check (list (option string)))
          "rendered" [ Some "1"; Some "5"; Some "3" ]
          (List.init 3 (Data.cell qty)));
    Alcotest.test_case "a null cell is None" `Quick (fun () ->
        Alcotest.(check (list (option string)))
          "middle is None" [ Some "rush"; None; Some "gift" ]
          (List.init 3 (Data.cell note)));
    Alcotest.test_case "floats render to two places" `Quick (fun () ->
        Alcotest.(check (list (option string)))
          "rendered" [ Some "49.50"; Some "18.00"; Some "240.00" ]
          (List.init 3 (Data.cell price)));
    Alcotest.test_case "find a column" `Quick (fun () ->
        Alcotest.(check (option string))
          "by name" (Some "note")
          (Option.map (fun (c : Data.t) -> c.name)
             (Data.find [ qty; note; price ] "note")));
    Alcotest.test_case "find a column that is not there" `Quick (fun () ->
        Alcotest.(check bool)
          "absent" true
          (Data.find [ qty; note; price ] "nope" = None)) ]

(* ---- the SQL we emit ---------------------------------------------------- *)

let orders_schema : Schema.t =
  { table = "orders";
    columns =
      [ { name = "id"; layout = Schema.Plain (Schema.Dense Schema.Int) };
        { name = "qty"; layout = Schema.Plain (Schema.Dense Schema.Int) };
        { name = "price"; layout = Schema.Plain (Schema.Dense Schema.Float) };
        { name = "sku"; layout = Schema.Plain Schema.Var };
        { name = "note"; layout = Schema.Nullable Schema.Var } ] }

let cols_named ns =
  List.filter_map (Schema.column orders_schema) ns

(* The central claim of the project is checkable here and nowhere else: the
   only SQL that ever leaves this process is a bulk column read. If a WHERE
   ever appears in [select_sql], the filter is being done by Postgres and the
   whole comparison is meaningless -- so it is asserted, not assumed. *)
let sql_tests =
  [ Alcotest.test_case "quote" `Quick (fun () ->
        Alcotest.(check string) "quoted" "\"orders\"" (Data.quote "orders"));
    Alcotest.test_case "count" `Quick (fun () ->
        Alcotest.(check string)
          "count" "SELECT count(*) FROM \"orders\""
          (Data.count_sql orders_schema));
    Alcotest.test_case "one column" `Quick (fun () ->
        Alcotest.(check string)
          "select" "SELECT \"qty\" FROM \"orders\""
          (Data.select_sql orders_schema (cols_named [ "qty" ])));
    Alcotest.test_case "several columns, in the order asked" `Quick (fun () ->
        Alcotest.(check string)
          "select" "SELECT \"price\", \"qty\" FROM \"orders\""
          (Data.select_sql orders_schema
             [ List.nth orders_schema.columns 2; List.nth orders_schema.columns 1 ]));
    Alcotest.test_case "no predicate is ever pushed down" `Quick (fun () ->
        let sql = Data.select_sql orders_schema (cols_named [ "id"; "qty" ]) in
        List.iter
          (fun forbidden ->
            Alcotest.(check bool)
              (forbidden ^ " must not appear")
              false (contains sql forbidden))
          [ "WHERE"; "where"; "ORDER"; "GROUP"; "LIMIT"; "count("; ">" ]) ]

(* ---- slots -------------------------------------------------------------- *)

let slot_shape (s : Data.slot) =
  (match s.values with
  | Data.Ints a -> Printf.sprintf "ints/%d" (Array.length a)
  | Data.Floats a -> Printf.sprintf "floats/%d" (Array.length a)
  | Data.Texts a -> Printf.sprintf "texts/%d" (Array.length a))
  ^ match s.valid with None -> " no-validity" | Some v -> Printf.sprintf " validity/%d" (Array.length v)

let allocates layout expected () =
  Alcotest.(check string)
    expected expected
    (slot_shape (Data.slot 3 { name = "c"; layout }))

(* The .mli decides the shape of memory, not just what the loop does. A Plain
   column has no validity array at all -- there is nothing to skip because
   there is nothing there. *)
let slot_tests =
  [ Alcotest.test_case "int" `Quick
      (allocates (Schema.Plain (Schema.Dense Schema.Int)) "ints/3 no-validity");
    Alcotest.test_case "int option" `Quick
      (allocates (Schema.Nullable (Schema.Dense Schema.Int)) "ints/3 validity/3");
    Alcotest.test_case "float" `Quick
      (allocates (Schema.Plain (Schema.Dense Schema.Float)) "floats/3 no-validity");
    Alcotest.test_case "string" `Quick
      (allocates (Schema.Plain Schema.Var) "texts/3 no-validity");
    Alcotest.test_case "string option" `Quick
      (allocates (Schema.Nullable Schema.Var) "texts/3 validity/3");
    Alcotest.test_case "bool is stored as 0 and 1" `Quick
      (allocates (Schema.Plain (Schema.Dense Schema.Bool)) "ints/3 no-validity");
    Alcotest.test_case "no rows" `Quick
      (allocates (Schema.Plain (Schema.Dense Schema.Int)) "ints/3 no-validity") ]

(* ---- storing one value -------------------------------------------------- *)

let qty_col : Schema.column =
  { name = "qty"; layout = Schema.Plain (Schema.Dense Schema.Int) }

let note_col : Schema.column =
  { name = "note"; layout = Schema.Nullable Schema.Var }

let store_tests =
  [ Alcotest.test_case "an int lands in the array" `Quick (fun () ->
        let s = Data.slot 3 qty_col in
        Data.store qty_col s 1 (Pgx.Value.of_int 42);
        match s.values with
        | Data.Ints a -> Alcotest.(check int) "written" 42 a.(1)
        | _ -> Alcotest.fail "expected an int slot");
    Alcotest.test_case "a string lands in the array" `Quick (fun () ->
        let s = Data.slot 3 note_col in
        Data.store note_col s 0 (Pgx.Value.of_string "rush");
        match s.values with
        | Data.Texts a -> Alcotest.(check string) "written" "rush" a.(0)
        | _ -> Alcotest.fail "expected a text slot");
    Alcotest.test_case "a float lands in the array" `Quick (fun () ->
        let c : Schema.column =
          { name = "price"; layout = Schema.Plain (Schema.Dense Schema.Float) }
        in
        let s = Data.slot 3 c in
        Data.store c s 2 (Pgx.Value.of_float 49.5);
        match s.values with
        | Data.Floats a -> Alcotest.(check (float 0.001)) "written" 49.5 a.(2)
        | _ -> Alcotest.fail "expected a float slot");
    Alcotest.test_case "NULL marks a nullable column absent" `Quick (fun () ->
        let s = Data.slot 3 note_col in
        Data.store note_col s 1 Pgx.Value.null;
        match s.valid with
        | Some v ->
            Alcotest.(check bool) "absent" false v.(1)
        | None -> Alcotest.fail "a nullable column should have a validity array");
    (* The one place the data can contradict the signature. Answering wrongly
       and quickly would be worse than stopping. *)
    Alcotest.test_case "NULL in a column the .mli said cannot be null" `Quick
      (fun () ->
        let s = Data.slot 3 qty_col in
        Alcotest.(check bool)
          "raises" true
          (try
             Data.store qty_col s 0 Pgx.Value.null;
             false
           with Failure _ -> true)) ]

(* ---- runner ------------------------------------------------------------- *)

let () =
  Alcotest.run "tatami"
    [ ("schema: parse_line", parse_line_tests);
      ("schema: split_arrow", split_arrow_tests);
      ("schema: layout_of_type", layout_of_type_tests);
      ("schema: lookups", lookup_tests);
      ("schema: read_file", read_file_tests);
      ("schema: load", load_tests);
      ("query: to_string", query_tests);
      ("query: operators", op_tests);
      ("lexer: tokenise", lexer_tests);
      ("lexer: errors", lexer_error_tests);
      ("parser: round trip", parser_tests);
      ("parser: errors", parser_error_tests);
      ("parser: helpers", parser_helper_tests);
      ("data: columns", data_tests);
      ("data: the SQL we emit", sql_tests);
      ("data: slots", slot_tests);
      ("data: store", store_tests) ]
