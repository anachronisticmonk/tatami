(* Load a corpus into Postgres.

   Every table-specific thing this needs -- what the tables are, what columns
   each has, what it holds collections of, how to read one of its rows -- is
   asked of [Loader], which the generator wrote. So there is no table name
   below, and adding a table to the corpus does not change this file.

   What is left is the part that is the same for every schema: descend the
   document, thread each row's key down to the rows that point at it, and hand
   batches to the database. Three things the JSON does not carry are supplied
   here -- the key of a document that has none, the key of the parent, and the
   position within a collection -- and they are the same three the layout
   marks as derived. *)

open Tatami
module Pg = Pgx_unix

let corpus = ref "corpus/ci.json"
let batch = ref 1000

(* ---- one table's pending rows -------------------------------------------- *)

type sink = {
  sql : string;
  mutable rows : Pgx.Value.t list list;
  mutable pending : int;
  mutable written : int;
}

(* Columns named rather than positional: the generated column order and the
   DDL's agree by construction, but saying so costs nothing and an INSERT that
   names its columns cannot be silently reordered. *)
let quote n = "\"" ^ n ^ "\""

let insert_sql table columns =
  let ps = List.mapi (fun i _ -> "$" ^ string_of_int (i + 1)) columns in
  Printf.sprintf "insert into %s (%s) values (%s)"
    (quote table)
    (String.concat ", " (List.map quote columns))
    (String.concat ", " ps)

let sink table =
  { sql = insert_sql table (Loader.columns table); rows = []; pending = 0; written = 0 }

(* One prepared statement, many parameter sets. Millions of rows is not a
   number of round trips worth making one at a time. *)
let flush conn s =
  if s.pending > 0 then begin
    ignore (Pg.execute_many conn ~query:s.sql ~params:(List.rev s.rows));
    s.written <- s.written + s.pending;
    s.rows <- [];
    s.pending <- 0
  end

let push conn s row =
  s.rows <- row :: s.rows;
  s.pending <- s.pending + 1;
  if s.pending >= !batch then flush conn s

(* ---- the walk ------------------------------------------------------------ *)

let rec walk conn sinks table ~parent ~pos ~doc =
  (* A document with no id of its own is given one here, before anything reads
     one. Its key is read twice -- for this row, and for the reference column
     in whatever points at it -- and creating it at each read would create two
     different keys for one row. Written into the document, both reads see the
     same value and nothing downstream has to know it was not always there. *)
  let doc = if Loader.mints table then Json.ensure_id doc (Mint.uuid ()) else doc in
  let doc =
    List.fold_left2
      (fun d member child ->
        if Loader.mints child then Json.ensure_member_id d member (Mint.uuid ()) else d)
      doc (Loader.ref_members table) (Loader.ref_tables table)
  in
  (* computed once and threaded down, so a row and everything pointing at it
     agree about its key *)
  let self = Loader.key table ~doc in
  push conn (List.assoc table sinks) (Loader.row table ~self ~parent ~pos ~doc);

  (* a member that was an object and became a table of its own. It sits in no
     collection, so it has neither a back reference nor a position. *)
  List.iter2
    (fun member child ->
      match Json.obj doc member with
      | `Null -> ()
      | o -> walk conn sinks child ~parent:Pgx.Value.null ~pos:(Bind.int 0) ~doc:o)
    (Loader.ref_members table) (Loader.ref_tables table);

  (* the collections this table holds. An array's elements are positioned by
     index and a map's entries are keyed by name; which one a table is came
     from its path, and the layout already recorded it. *)
  List.iter2
    (fun member child ->
      if Loader.keyed child then
        List.iter
          (fun (k, v) -> walk conn sinks child ~parent:self ~pos:(Bind.string k) ~doc:v)
          (Json.entries doc member)
      else
        List.iteri
          (fun i v -> walk conn sinks child ~parent:self ~pos:(Bind.int i) ~doc:v)
          (Json.arr doc member))
    (Loader.child_members table) (Loader.child_tables table)

(* ---- driving ------------------------------------------------------------- *)

let () =
  let rec args = function
    | "--corpus" :: v :: r -> corpus := v; args r
    | "--batch" :: v :: r -> batch := int_of_string v; args r
    | [] -> ()
    | a :: _ -> prerr_endline ("unknown argument " ^ a); exit 2
  in
  args (List.tl (Array.to_list Sys.argv));
  let t0 = Unix.gettimeofday () in
  let sinks = List.map (fun t -> (t, sink t)) Loader.tables in

  Pg.with_conn ~ssl:`No ~host:Data.host ~port:Data.port ~user:Data.user
    ~password:Data.password ~database:Data.database (fun conn ->
      Pg.with_transaction conn (fun conn ->
          (* reverse order: a table is dropped before the tables it points into *)
          List.iter
            (fun t ->
              Pg.execute_unit conn (Printf.sprintf "drop table if exists %s cascade" (quote t)))
            (List.rev Loader.tables);
          List.iter (fun d -> Pg.execute_unit conn d) Loader.ddl;
          prerr_endline ("created " ^ string_of_int (List.length Loader.tables) ^ " tables");

          let n = Corpus.iter_json !corpus ~f:(fun doc ->
              walk conn sinks Loader.root ~parent:Pgx.Value.null ~pos:(Bind.int 0) ~doc)
          in
          List.iter (fun (_, s) -> flush conn s) sinks;

          (* held back until the rows are in: validating a reference per row
             while millions are loading is the load's cost, and applied
             afterwards they are checked once, in bulk *)
          List.iter (fun c -> Pg.execute_unit conn c) Loader.constraints;
          Printf.eprintf "%d documents in %.1fs\n" n (Unix.gettimeofday () -. t0)));

  List.iter (fun (t, s) -> Printf.eprintf "  %-14s %9d rows\n" t s.written) sinks;
  Printf.eprintf "%!"
