(* The measurements behind docs/phase_3/measurements.tex.

   Every number in that document comes from here, so the document can be
   rebuilt rather than believed:

     ./db/up.sh && ./db/seed.sh 200000
     dune exec bin/bench.exe

   Timings are a median of several runs, not a mean: one slow sample from a
   page fault or a checkpoint should not move the figure. Even so the variance
   between whole runs is a few percent, and no conclusion below rests on a
   difference smaller than that. *)

open Tatami

let now = Unix.gettimeofday
let ms t = t *. 1000.

let median xs =
  let a = Array.of_list xs in
  Array.sort compare a;
  a.(Array.length a / 2)

let best ?(n = 7) f =
  let rec go k acc =
    if k = 0 then acc
    else
      let t0 = now () in
      let x = f () in
      go (k - 1) ((now () -. t0, x) :: acc)
  in
  let rs = go n [] in
  (median (List.map fst rs), snd (List.hd rs))

let data_dir = "docs/phase_3/data"

let emit name rows =
  let path = Filename.concat data_dir name in
  let oc = open_out path in
  List.iter (fun l -> output_string oc (l ^ "\n")) rows;
  close_out oc;
  Printf.printf "  wrote %s\n%!" path

let rule n = print_endline (String.make n '-')

(* ---- 1. materialising a result set -------------------------------------- *)

(* Both kernels stream. What differs is where the values land: boxed text, or
   a dense array of the type the .mli named. *)
let materialise schema =
  print_endline "\n1. materialising a result set (200k rows)";
  Printf.printf "%-34s %9s %9s %8s\n" "query" "plain" "tuned" "win";
  rule 64;
  let rows =
    List.map
      (fun (sql, label) ->
        let q = Parser.parse sql in
        let tp, _ = best (fun () -> Plain.run q) in
        let tt, _ = best (fun () -> Tuned.run schema q) in
        let win = (tp -. tt) /. tp *. 100. in
        Printf.printf "%-34s %8.2f %9.2f %7.0f%%\n" sql (ms tp) (ms tt) win;
        Printf.sprintf "%s %.2f %.2f %.1f" label (ms tp) (ms tt) win)
      [ ("select qty from orders", "int");
        ("select qty, price from orders", "int+float");
        ("select note from orders", "opt-text");
        ("select * from orders", "all-six") ]
  in
  emit "materialise.dat" ("layout plain tuned win" :: rows)

(* ---- 2. what a column costs --------------------------------------------- *)

(* Added one at a time, so the marginal cost of each is visible. The point is
   that the .mli predicts this table: the expensive column is the one whose
   type says [string option]. *)
let columns schema =
  print_endline "\n2. marginal cost of each column (tuned, 200k rows)";
  Printf.printf "%-3s %-14s %-16s %9s %9s\n" "n" "added" "layout" "total" "marginal";
  rule 56;
  let cols = [ "qty"; "id"; "customer_id"; "price"; "sku"; "note" ] in
  let prev = ref 0. in
  let rows =
    List.mapi
      (fun i name ->
        let take = List.filteri (fun j _ -> j <= i) cols in
        let q =
          Parser.parse (Printf.sprintf "select %s from orders" (String.concat ", " take))
        in
        let tt, _ = best ~n:5 (fun () -> Tuned.run schema q) in
        let layout =
          match Schema.column schema name with
          | Some c -> Schema.layout_to_string c.layout
          | None -> "?"
        in
        let marginal = ms tt -. !prev in
        Printf.printf "%-3d %-14s %-16s %8.2f %+9.2f\n" (i + 1) name layout (ms tt) marginal;
        prev := ms tt;
        (* hyphens, not underscores: this lands in a LaTeX symbolic coord *)
        let label = String.map (function '_' -> '-' | c -> c) name in
        Printf.sprintf "%d %s %.2f %.2f" (i + 1) label (ms tt) marginal)
      cols
  in
  emit "columns.dat" ("n added total marginal" :: rows)

(* ---- 3. load once, query many ------------------------------------------- *)

(* The workload the claim actually needs. Shredding text into arrays is only
   worth paying for if something then runs over the arrays more than once. *)
let corpus_sql = "select id, customer_id, sku, qty, price, note from orders"
let corpus_names = [ "id"; "customer_id"; "sku"; "qty"; "price"; "note" ]

let workload =
  [ ("select qty from orders where qty > 500", "int-half-survive");
    ("select sku from orders where qty = 42", "int-few-equality");
    ("select note from orders where price > 500.0", "float-half-survive");
    ("select id from orders where sku > 'BENCH-050000'", "text-compare");
    ("select qty, price from orders where qty < 10", "int-few-lessthan") ]

let load_once_query_many schema =
  print_endline "\n3. load once, query many";
  let cq = Parser.parse corpus_sql in
  let lp, prows = best ~n:5 (fun () -> Plain.run cq) in
  let lt, tcols = best ~n:5 (fun () -> Tuned.run schema cq) in
  Printf.printf "   load (%d rows): plain %.1fms  tuned %.1fms\n\n" (List.length prows)
    (ms lp) (ms lt);
  Printf.printf "%-50s %8s %8s %7s\n" "then, in memory" "plain" "tuned" "speedup";
  rule 76;
  let tot_p = ref 0. and tot_t = ref 0. in
  let rows =
    List.map
      (fun (sql, label) ->
        let q = Parser.parse sql in
        let tp, a = best (fun () -> Plain.query corpus_names q prows) in
        let tt, b = best (fun () -> Tuned.query schema tcols q) in
        let nb = match b with [] -> 0 | c :: _ -> Data.length c in
        if List.length a <> nb then
          Printf.printf "  !! disagreement: plain %d rows, tuned %d\n" (List.length a) nb;
        tot_p := !tot_p +. tp;
        tot_t := !tot_t +. tt;
        Printf.printf "%-50s %7.2f %8.2f %6.1fx\n" sql (ms tp) (ms tt) (tp /. tt);
        Printf.sprintf "%s %.2f %.2f %.2f" label (ms tp) (ms tt) (tp /. tt))
      workload
  in
  rule 76;
  Printf.printf "%-50s %7.2f %8.2f %6.1fx\n\n" "one round of all five" (ms !tot_p) (ms !tot_t)
    (!tot_p /. !tot_t);
  emit "workload.dat" ("label plain tuned speedup" :: rows);
  let rounds =
    List.map
      (fun k ->
        let p = lp +. (float_of_int k *. !tot_p) and t = lt +. (float_of_int k *. !tot_t) in
        Printf.printf "    k=%-4d plain %8.1fms  tuned %8.1fms  %.2fx\n" k (ms p) (ms t)
          (p /. t);
        Printf.sprintf "%d %.2f %.2f %.3f" k (ms p) (ms t) (p /. t))
      [ 0; 1; 2; 5; 10; 20; 50; 100 ]
  in
  emit "rounds.dat" ("k plain tuned ratio" :: rounds)

let () =
  let schema = Schema.load "schema/orders.mli" in
  let n =
    match Data.fetch "select count(*) from orders" with
    | [ [ v ] ] -> Option.value (Pgx.Value.to_int v) ~default:0
    | _ -> 0
  in
  Printf.printf "tatami bench: %s, %d rows\n" schema.table n;
  if n < 100_000 then
    print_endline "  (few rows -- run ./db/seed.sh 200000 for the numbers in the paper)";
  materialise schema;
  columns schema;
  load_once_query_many schema;
  print_endline "\ndone."
