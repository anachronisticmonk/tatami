(* The differential: one query, both kernels, and what separates them.

   §5 has two halves and this file is both. The correctness half is that the
   two must return the same rows -- if they ever disagree the speed question is
   void, so [agree] is checked on every run and not only when someone asks.
   The measurement half is the phases below.

   Timing is split rather than totalled on purpose. Both kernels pay the same
   round trip, and reporting one number would hide that the only part the .mli
   touches is what happens after the rows arrive. Allocation is reported too,
   and is the more honest figure: a wall clock on a warm page cache is mostly
   noise, while words allocated is exactly the thing a dense array avoids. *)

type phase = { name : string; seconds : float }

type outcome = {
  kernel : string;
  sql : string;
  columns : string list;
  rows : string option list list;
  phases : phase list;
  seconds : float;
  words : float;  (* minor words allocated, the cost of the representation *)
}

type t = {
  query : Query.t;
  plain : outcome;
  tuned : outcome;
  agree : bool;
}

let now = Unix.gettimeofday

(* [Gc.minor_words] counts allocation since the program began, so a difference
   across a call is what that call allocated. Major-heap promotions are not
   counted; for these sizes almost everything stays minor. *)
let timed name f =
  let w0 = Gc.minor_words () and t0 = now () in
  let x = f () in
  let dt = now () -. t0 and dw = Gc.minor_words () -. w0 in
  (x, { name; seconds = dt }, dw)

(* A tuned column becomes text only here, at the edge. That conversion is a
   cost of the typed representation when the destination is a web page, and it
   is reported as its own phase rather than folded into the total -- printing
   is not what the arrays are for. *)
let rows_of_columns (cols : Data.t list) =
  let n = match cols with [] -> 0 | c :: _ -> Data.length c in
  List.init n (fun i -> List.map (fun c -> Data.cell c i) cols)

let plain (q : Query.t) =
  let sql = Plain.sql q in
  let rows, fetch, w1 = timed "fetch" (fun () -> Data.fetch sql) in
  let out, render, w2 =
    timed "render" (fun () -> List.map (List.map Pgx.Value.to_string) rows)
  in
  { kernel = "plain";
    sql;
    (* Without a signature the column names are not known; the rows do not
       carry them and asking Postgres would be another round trip. *)
    columns = [];
    rows = out;
    phases = [ fetch; render ];
    seconds = fetch.seconds +. render.seconds;
    words = w1 +. w2 }

let tuned (schema : Schema.t) (q : Query.t) =
  let sql = Tuned.sql schema q in
  let names = Tuned.wanted schema q in
  let cols = List.map (Tuned.column schema) names in
  let rows, fetch, w1 = timed "fetch" (fun () -> Data.fetch sql) in
  let data, decode, w2 = timed "decode" (fun () -> Tuned.decode cols rows) in
  let out, render, w3 = timed "render" (fun () -> rows_of_columns data) in
  { kernel = "tuned";
    sql;
    columns = names;
    rows = out;
    phases = [ fetch; decode; render ];
    seconds = fetch.seconds +. decode.seconds +. render.seconds;
    words = w1 +. w2 +. w3 }

(* Validation belongs to neither kernel. [Analysis.plan] rejects a query the
   signature cannot describe, and it must reject it for both or the two would
   answer different questions -- [plain] would happily compare an int column
   against 4.5 and Postgres would agree with it. *)
let once (schema : Schema.t) (q : Query.t) =
  ignore (Analysis.plan schema q);
  let plain = plain q in
  let tuned = tuned schema q in
  { query = q; plain; tuned; agree = plain.rows = tuned.rows }

(* A median run rather than an averaged one: the reported phases then belong to
   a sample that actually happened, instead of being a composite of runs that
   never occurred together. The first run is discarded -- it pays for the
   connection and a cold page cache, and reporting it would say more about the
   machine than about the kernels. *)
let median ?(n = 5) schema q =
  ignore (once schema q);
  let rs = List.init n (fun _ -> once schema q) in
  let total r = r.plain.seconds +. r.tuned.seconds in
  let sorted = List.sort (fun a b -> Stdlib.compare (total a) (total b)) rs in
  List.nth sorted (n / 2)
