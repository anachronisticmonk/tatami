(* The derived-schema path: one dense typed array per column.

   What each column *is* comes from the .mli and from nowhere else. The array
   type is chosen by the layout the schema reader parsed, and a validity mask
   is allocated only where that layout says [option] -- so a column the
   signature calls total has no mask, no branch, and no memory holding either.
   Nothing here special-cases a column by name.

   Shredding is the cost. The corpus arrives as documents and leaves as seven
   tables of columns, which means every value is moved once, and the nesting
   that row-major keeps for free has to be rebuilt from keys whenever a query
   needs it. That is the trade being measured. *)

open Tatami

(* ---- building a column --------------------------------------------------- *)

(* Grown by doubling rather than sized in advance: the row count is not known
   until the corpus has been read, and counting it first would mean reading
   1.5 GB twice. *)
type builder = {
  b_name : string;
  mutable v : Data.values;
  mutable valid : bool array option;
  mutable n : int;
}

let cap b =
  match b.v with
  | Data.Ints a -> Array.length a
  | Data.Floats a -> Array.length a
  | Data.Texts a -> Array.length a

(* The whole claim of this module, in one function: the layout decides the
   array type, and the constructor decides whether a mask exists at all. *)
let builder (c : Schema.column) =
  let shape, valid =
    match c.layout with
    | Schema.Plain s -> (s, None)
    | Schema.Nullable s -> (s, Some (Array.make 1024 false))
  in
  let v =
    match shape with
    | Schema.Dense Schema.Int | Schema.Dense Schema.Bool -> Data.Ints (Array.make 1024 0)
    | Schema.Dense Schema.Float -> Data.Floats (Array.make 1024 0.)
    | Schema.Var -> Data.Texts (Array.make 1024 "")
  in
  { b_name = c.name; v; valid; n = 0 }

let grow b =
  let m = 2 * cap b in
  let blit make a = let x = make m in Array.blit a 0 x 0 b.n; x in
  b.v <-
    (match b.v with
    | Data.Ints a -> Data.Ints (blit (fun m -> Array.make m 0) a)
    | Data.Floats a -> Data.Floats (blit (fun m -> Array.make m 0.) a)
    | Data.Texts a -> Data.Texts (blit (fun m -> Array.make m "") a));
  match b.valid with
  | None -> ()
  | Some x -> b.valid <- Some (blit (fun m -> Array.make m false) x)

let room b = if b.n >= cap b then grow b

(* A present value. The mask is only written where one exists -- for a total
   column there is nothing to write to, which is the point. *)
let put_int b x =
  room b;
  (match b.v with Data.Ints a -> a.(b.n) <- x | _ -> invalid_arg b.b_name);
  (match b.valid with Some m -> m.(b.n) <- true | None -> ());
  b.n <- b.n + 1

let put_float b x =
  room b;
  (match b.v with Data.Floats a -> a.(b.n) <- x | _ -> invalid_arg b.b_name);
  (match b.valid with Some m -> m.(b.n) <- true | None -> ());
  b.n <- b.n + 1

let put_text b x =
  room b;
  (match b.v with Data.Texts a -> a.(b.n) <- x | _ -> invalid_arg b.b_name);
  (match b.valid with Some m -> m.(b.n) <- true | None -> ());
  b.n <- b.n + 1

(* Absent. The slot keeps its initialiser, and only the mask says the
   initialiser is not a value -- which is why a total column can never take
   this path: it has no mask to record the absence in. *)
let put_null b =
  room b;
  (match b.valid with
  | Some m -> m.(b.n) <- false
  | None ->
      failwith (b.b_name ^ " is NULL in the data, but its signature says otherwise"));
  b.n <- b.n + 1

let finish b : Data.t =
  let take a = Array.sub a 0 b.n in
  { Data.name = b.b_name;
    values =
      (match b.v with
      | Data.Ints a -> Data.Ints (take a)
      | Data.Floats a -> Data.Floats (take a)
      | Data.Texts a -> Data.Texts (take a));
    valid = Option.map take b.valid }

(* ---- a table ------------------------------------------------------------- *)

type table = { t_name : string; cols : (string * builder) list }

let table (s : Schema.t) =
  { t_name = s.table; cols = List.map (fun c -> (c.Schema.name, builder c)) s.columns }

let col t name =
  match List.assoc_opt name t.cols with
  | Some b -> b
  | None -> failwith (Printf.sprintf "no column %s in %s" name t.t_name)

(* ---- the store ----------------------------------------------------------- *)

let name = "columnar"

type t = { tables : (string * Data.t list) list; rows : (string * int) list }

let get t tbl c : Data.t =
  match List.assoc_opt tbl t.tables with
  | None -> failwith ("no table " ^ tbl)
  | Some cs -> (
      match List.find_opt (fun (d : Data.t) -> d.name = c) cs with
      | Some d -> d
      | None -> failwith (Printf.sprintf "no column %s.%s" tbl c))

let ints t tbl c = match (get t tbl c).values with Data.Ints a -> a | _ -> invalid_arg c
let floats t tbl c = match (get t tbl c).values with Data.Floats a -> a | _ -> invalid_arg c
let texts t tbl c = match (get t tbl c).values with Data.Texts a -> a | _ -> invalid_arg c

(* ---- shredding ----------------------------------------------------------- *)

open Yojson.Safe.Util

let gi k j = to_int (member k j)
let gs k j = to_string (member k j)
let gb k j = to_bool (member k j)
let gf k j = match member k j with `Float f -> f | `Int n -> float_of_int n | _ -> 0.
let arr k j = match member k j with `List l -> l | _ -> []
let opt_text b k j = match member k j with `String x -> put_text b x | _ -> put_null b
let opt_int b k j = match member k j with `Int x -> put_int b x | _ -> put_null b

let load path =
  let schemas = Schema.load_dir "schema" in
  let of_name n =
    match Schema.table schemas n with
    | Some s -> table s
    | None -> failwith ("no schema for " ^ n)
  in
  let repo = of_name "repo" and run = of_name "run"
  and job = of_name "job" and step = of_name "step" in

  ignore
    (Corpus.iter_json path ~f:(fun r ->
         let rid = gs "id" r in
         put_text (col repo "id") rid;
         put_text (col repo "name") (gs "name" r);
         put_text (col repo "org") (gs "org" r);
         put_int (col repo "is_private") (if gb "private" r then 1 else 0);

         List.iteri
           (fun ri u ->
             let uid = gi "id" u in
             put_int (col run "id") uid;
             put_text (col run "repo_id") rid;
             put_int (col run "idx") ri;
             put_text (col run "branch") (gs "branch" u);
             put_text (col run "status") (gs "status" u);
             put_int (col run "ms") (gi "ms" u);
             opt_text (col run "trigger") "trigger" u;

             List.iteri
               (fun ji j ->
                 let jid = gi "id" j in
                 put_int (col job "id") jid;
                 put_int (col job "run_id") uid;
                 put_int (col job "idx") ji;
                 put_text (col job "os") (gs "os" j);
                 put_text (col job "status") (gs "status" j);
                 put_int (col job "ms") (gi "ms" j);
                 opt_int (col job "exit") "exit" j;

                 List.iteri
                   (fun si s ->
                     put_int (col step "id") (gi "id" s);
                     put_int (col step "job_id") jid;
                     put_int (col step "idx") si;
                     put_text (col step "name") (gs "name" s);
                     put_int (col step "ms") (gi "ms" s);
                     put_float (col step "rate") (gf "rate" s);
                     opt_text (col step "error") "error" s)
                   (arr "steps" j))
               (arr "jobs" u))
           (arr "runs" r)));

  let freeze t = (t.t_name, List.map (fun (_, b) -> finish b) t.cols) in
  let ts = List.map freeze [ repo; run; job; step ] in
  { tables = ts;
    rows = List.map (fun (n, cs) -> (n, match cs with [] -> 0 | c :: _ -> Data.length c)) ts }

let footprint (_ : t) =
  Gc.full_major ();
  float_of_int (Gc.stat ()).live_words

(* ---- the queries --------------------------------------------------------- *)

(* Every scan below reads one or two arrays end to end and touches nothing
   else. The other columns of a step are not in the way, not in the cache line,
   and not paged in. *)

let scan t threshold =
  let d = ints t "step" "ms" in
  let n = ref 0 in
  for i = 0 to Array.length d - 1 do
    if Array.unsafe_get d i > threshold then incr n
  done;
  Workload.Count !n

(* Two dense arrays walked in step. Both columns are total in the .mli, so
   there is no mask to consult on either and no branch for absence -- and the
   product they compute needs no mask of its own for the same reason. *)
let computed t threshold =
  let d = ints t "step" "ms" and c = floats t "step" "rate" in
  let acc = ref 0. in
  for i = 0 to Array.length d - 1 do
    let x = Array.unsafe_get d i in
    if x > threshold then acc := !acc +. (float_of_int x *. Array.unsafe_get c i)
  done;
  Workload.Sum_float !acc

let by_status t =
  let s = texts t "step" "name" and d = ints t "step" "ms" in
  let tbl = Hashtbl.create 8 in
  for i = 0 to Array.length d - 1 do
    let k = Array.unsafe_get s i and v = Array.unsafe_get d i in
    let cur = try Hashtbl.find tbl k with Not_found -> 0 in
    if v > cur then Hashtbl.replace tbl k v
  done;
  Workload.Groups (List.sort compare (Hashtbl.fold (fun k v a -> (k, v) :: a) tbl []))

(* A set of keys, for following one from table to table. This is the join
   row-major does not have to do: it already holds the children inside the
   parent, where the columnar store holds them in a different array entirely. *)
let idset ids =
  let h = Hashtbl.create (Array.length ids * 2) in
  Array.iter (fun i -> Hashtbl.replace h i ()) ids;
  h

let children ~key ~id keep =
  let out = ref [] in
  for i = Array.length key - 1 downto 0 do
    if Hashtbl.mem keep (Array.unsafe_get key i) then out := Array.unsafe_get id i :: !out
  done;
  idset (Array.of_list !out)

(* The reassembly, and the case this layout should lose. There is no
   repo-shaped object here: finding one document's steps means scanning run,
   then job, then step -- three full passes to gather what row-major had
   contiguously all along. *)
let document t id =
  let rid = texts t "repo" "id" in
  if not (Array.exists (fun x -> String.equal x id) rid) then Workload.Missing
  else
    let keep = Hashtbl.create 2 in
    Hashtbl.replace keep id ();
    let runs = children ~key:(texts t "run" "repo_id") ~id:(ints t "run" "id") keep in
    let jobs = children ~key:(ints t "job" "run_id") ~id:(ints t "job" "id") runs in
    let sk = ints t "step" "job_id" and sd = ints t "step" "ms" in
    let steps = ref 0 and ms = ref 0 in
    for i = 0 to Array.length sk - 1 do
      if Hashtbl.mem jobs (Array.unsafe_get sk i) then (
        incr steps;
        ms := !ms + Array.unsafe_get sd i)
    done;
    Workload.Row
      (List.map string_of_int [ Hashtbl.length runs; Hashtbl.length jobs; !steps; !ms ])

(* Three hops, and every one of them a scan. Row-major walks pointers it
   already holds; this has to rebuild the relationship from keys. *)
let three_hop t org =
  let o = texts t "repo" "org" and rid = texts t "repo" "id" in
  let keep = Hashtbl.create 1024 in
  for i = 0 to Array.length o - 1 do
    if String.equal (Array.unsafe_get o i) org then
      Hashtbl.replace keep (Array.unsafe_get rid i) ()
  done;
  let runs = children ~key:(texts t "run" "repo_id") ~id:(ints t "run" "id") keep in
  let jobs = children ~key:(ints t "job" "run_id") ~id:(ints t "job" "id") runs in
  let sk = ints t "step" "job_id" and sd = ints t "step" "ms" in
  let total = ref 0 in
  for i = 0 to Array.length sk - 1 do
    if Hashtbl.mem jobs (Array.unsafe_get sk i) then total := !total + Array.unsafe_get sd i
  done;
  Workload.Sum_int !total
