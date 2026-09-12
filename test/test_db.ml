(* The one test that needs a live database.

   Deliberately not a (test) stanza, so `dune test` stays hermetic and fast.
   Run it by hand when the container is up:

     ./db/up.sh                    (or: docker start tatami-pg)
     dune exec test/test_db.exe

   What it checks is the seam nothing else can: that the columns Postgres
   sends back land in arrays whose shape matches what the .mli promised. Every
   specialisation downstream rests on that, and it is the only place the
   promise meets real data. *)

open Tatami

let schema = Schema.load "schema/orders.mli"

let shape (c : Data.t) =
  (match c.values with
  | Data.Ints _ -> "ints"
  | Data.Floats _ -> "floats"
  | Data.Texts _ -> "texts")
  ^ match c.valid with None -> ", no validity array" | Some _ -> ", validity array"

let load_tests =
  [ Alcotest.test_case "one column comes back" `Quick (fun () ->
        let cols = Data.load schema [ "qty" ] in
        Alcotest.(check int) "one column" 1 (List.length cols);
        Alcotest.(check bool) "some rows" true (Data.length (List.hd cols) > 0));
    Alcotest.test_case "several columns, in the order asked" `Quick (fun () ->
        let cols = Data.load schema [ "id"; "sku"; "price" ] in
        Alcotest.(check (list string))
          "order preserved" [ "id"; "sku"; "price" ]
          (List.map (fun (c : Data.t) -> c.name) cols));
    Alcotest.test_case "all columns are the same length" `Quick (fun () ->
        let cols = Data.load schema [ "id"; "qty"; "note" ] in
        match List.map Data.length cols with
        | n :: rest ->
            Alcotest.(check (list int))
              "equal lengths"
              (List.map (fun _ -> n) rest)
              rest
        | [] -> Alcotest.fail "no columns");
    (* The signature decides the shape of memory. A column the .mli calls
       [int] arrives with no validity array; one it calls [string option]
       arrives with one. *)
    Alcotest.test_case "the .mli decides what is allocated" `Quick (fun () ->
        let cols = Data.load schema [ "qty"; "price"; "sku"; "note" ] in
        Alcotest.(check (list string))
          "shapes"
          [ "ints, no validity array";
            "floats, no validity array";
            "texts, no validity array";
            "texts, validity array" ]
          (List.map shape cols));
    Alcotest.test_case "a column that does not exist" `Quick (fun () ->
        Alcotest.(check bool)
          "raises" true
          (try
             ignore (Data.load schema [ "nonsense" ]);
             false
           with Failure _ -> true)) ]

let () =
  print_endline
    (Printf.sprintf "reading %s from %s@%s:%d" schema.table Data.database
       Data.host Data.port);
  Alcotest.run ~and_exit:false "tatami (live database)"
    [ ("data: load", load_tests) ]
