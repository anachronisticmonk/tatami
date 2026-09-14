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

(* Grown in fixed chunks rather than by doubling.

   The row count is not known until the corpus has been read, and counting it
   first would mean parsing 1.5 GB twice -- the parse being the expensive part,
   that cure is worse than the disease. Doubling was the first answer and it
   scaled badly: every doubling copies the whole array, and a final trim copies
   it once more, so filling n elements moves about 3n of them through the major
   heap. At thirteen million elements that showed up as a 2.6x penalty over the
   row-major store, which is most of what set the crossover.

   Chunks move exactly n. Nothing is copied while filling; one exact array is
   allocated at the end and each chunk blitted into it once. Peak memory is 2n
   at that moment rather than 3n during a doubling. *)

let chunk = 65536

type builder = {
  b_name : string;
  (* completed chunks, newest first *)
  mutable full : Data.values list;
  mutable full_masks : bool array list;
  mutable cur : Data.values;
  mutable cur_mask : bool array option;
  mutable in_cur : int;
  mutable total : int;
}

let fresh_values proto n =
  match proto with
  | Data.Ints _ -> Data.Ints (Array.make n 0)
  | Data.Floats _ -> Data.Floats (Array.make n 0.)
  | Data.Texts _ -> Data.Texts (Array.make n "")

(* The whole claim of this module, in one function: the layout decides the
   array type, and the constructor decides whether a mask exists at all. *)
let builder (c : Schema.column) =
  let shape, masked =
    match c.layout with
    | Schema.Plain s -> (s, false)
    | Schema.Nullable s -> (s, true)
  in
  let cur =
    match shape with
    | Schema.Dense Schema.Int | Schema.Dense Schema.Bool -> Data.Ints (Array.make chunk 0)
    | Schema.Dense Schema.Float -> Data.Floats (Array.make chunk 0.)
    | Schema.Var -> Data.Texts (Array.make chunk "")
  in
  { b_name = c.name; full = []; full_masks = [];
    cur; cur_mask = (if masked then Some (Array.make chunk false) else None);
    in_cur = 0; total = 0 }

let rotate b =
  b.full <- b.cur :: b.full;
  b.cur <- fresh_values b.cur chunk;
  (match b.cur_mask with
  | None -> ()
  | Some m ->
      b.full_masks <- m :: b.full_masks;
      b.cur_mask <- Some (Array.make chunk false));
  b.in_cur <- 0

let room b = if b.in_cur >= chunk then rotate b

let bump b present =
  (match b.cur_mask with Some m -> m.(b.in_cur) <- present | None -> ());
  b.in_cur <- b.in_cur + 1;
  b.total <- b.total + 1

(* A present value. The mask is only written where one exists -- for a total
   column there is nothing to write to, which is the point. *)
let put_int b x =
  room b;
  (match b.cur with Data.Ints a -> a.(b.in_cur) <- x | _ -> invalid_arg b.b_name);
  bump b true

let put_float b x =
  room b;
  (match b.cur with Data.Floats a -> a.(b.in_cur) <- x | _ -> invalid_arg b.b_name);
  bump b true

let put_text b x =
  room b;
  (match b.cur with Data.Texts a -> a.(b.in_cur) <- x | _ -> invalid_arg b.b_name);
  bump b true

(* Absent. The slot keeps its initialiser, and only the mask says the
   initialiser is not a value -- which is why a total column can never take
   this path: it has no mask to record the absence in. *)
let put_null b =
  room b;
  (match b.cur_mask with
  | Some _ -> ()
  | None ->
      failwith (b.b_name ^ " is NULL in the data, but its signature says otherwise"));
  bump b false

(* One exact array, filled by blitting each chunk in once. *)
let finish b : Data.t =
  let n = b.total in
  let chunks = List.rev (b.cur :: b.full) in
  let values = fresh_values b.cur n in
  let at = ref 0 in
  List.iter
    (fun c ->
      let len = min chunk (n - !at) in
      if len > 0 then (
        (match (c, values) with
        | Data.Ints src, Data.Ints dst -> Array.blit src 0 dst !at len
        | Data.Floats src, Data.Floats dst -> Array.blit src 0 dst !at len
        | Data.Texts src, Data.Texts dst -> Array.blit src 0 dst !at len
        | _ -> invalid_arg b.b_name);
        at := !at + len))
    chunks;
  let valid =
    match b.cur_mask with
    | None -> None
    | Some last ->
        let dst = Array.make n false in
        let at = ref 0 in
        List.iter
          (fun src ->
            let len = min chunk (n - !at) in
            if len > 0 then (Array.blit src 0 dst !at len; at := !at + len))
          (List.rev (last :: b.full_masks));
        Some dst
  in
  { Data.name = b.b_name; values; valid }

(* ---- a table ------------------------------------------------------------- *)

type table = { t_name : string; cols : (string * builder) list }

let table (s : Schema.t) =
  { t_name = s.table; cols = List.map (fun c -> (c.Schema.name, builder c)) s.columns }

let col t name =
  match List.assoc_opt name t.cols with
  | Some b -> b
  | None -> failwith (Printf.sprintf "no column %s in %s" name t.t_name)

(* ---- where a parent's children live -------------------------------------- *)

(* The structural fact the join has been throwing away.

   Shredding walks documents depth-first, so every run of one repo is written
   before any run of the next. The child table is therefore *grouped* by its
   parent key: a parent's children occupy one contiguous block of rows, and
   [idx] restarting at 0 is the witness.

   That is not a statistic. It follows from the parent-child relationship
   having been an array -- [coll] in the Lean model -- plus the order shredding
   visits documents in. A database would need an index, or a CLUSTER, to know
   the same thing.

   With it, following a key stops being a scan of the whole child table and
   becomes a slice. Without it, the fallback is the scan we had. So the index
   checks as it builds: if any parent's rows turn out to be interrupted, the
   grouping claim is false and the slices are not used. *)

(* Offsets, not a hashtable.

   Children are grouped by parent *and in parent order*: repo row 0's runs come
   first, then repo row 1's. So the whole relationship is one int array of
   length |parent| + 1, where parent i owns child rows [off.(i), off.(i+1)).
   Following a key becomes an array index -- no hashing, no probe, and no index
   on the parent's key that the row-major store would not also have.

   This is Arrow's list layout, arrived at from the schema rather than adopted:
   it is what [coll] means once the documents have been flattened.

   Built by walking the child's key column and cutting a block each time the
   key changes. If the number of blocks does not match the number of parents,
   the grouping does not hold -- a corpus shredded in some other order, or a
   parent with no children -- and the offsets are refused rather than trusted. *)
type offsets = { off : int array; valid : bool }

let no_offsets = { off = [||]; valid = false }

let build_offsets (type k) ~(parents : int) (key : k array) : offsets =
  let n = Array.length key in
  let off = Array.make (parents + 1) 0 in
  let blocks = ref 0 and i = ref 0 in
  (try
     while !i < n do
       if !blocks >= parents then raise Exit;
       off.(!blocks) <- !i;
       let k = Array.unsafe_get key !i in
       incr i;
       while !i < n && Array.unsafe_get key !i = k do incr i done;
       incr blocks
     done
   with Exit -> ());
  if !blocks = parents && !i = n then (off.(parents) <- n; { off; valid = true })
  else no_offsets

let span o i = (o.off.(i), o.off.(i + 1) - o.off.(i))

(* ---- the store ----------------------------------------------------------- *)

let name = "columnar"

type t = {
  tables : (string * Data.t list) list;
  rows : (string * int) list;
  mutable runs_of : offsets;   (* repo row -> its rows in run  *)
  mutable jobs_of : offsets;   (* run row  -> its rows in job  *)
  mutable steps_of : offsets;  (* job row  -> its rows in step *)
  (* the one lookup neither layout gets for free: a uuid to a row. The
     row-major store is given the same, so this is not an index one side has
     and the other does not. *)
  mutable repo_at : (string, int) Hashtbl.t;
}

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
  let store =
    { tables = ts;
      rows = List.map (fun (n, cs) -> (n, match cs with [] -> 0 | c :: _ -> Data.length c)) ts;
      runs_of = no_offsets; jobs_of = no_offsets; steps_of = no_offsets;
      repo_at = Hashtbl.create 16 }
  in
  let rows n = match List.assoc_opt n store.rows with Some k -> k | None -> 0 in
  store.runs_of <- build_offsets ~parents:(rows "repo") (texts store "run" "repo_id");
  store.jobs_of <- build_offsets ~parents:(rows "run") (ints store "job" "run_id");
  store.steps_of <- build_offsets ~parents:(rows "job") (ints store "step" "job_id");
  let rid = texts store "repo" "id" in
  Array.iteri (fun i k -> Hashtbl.replace store.repo_at k i) rid;
  store

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

(* ---- the fallback: following a key by scanning ---------------------------- *)

(* What this did before the grouping was noticed, kept because the grouping is
   checked rather than assumed: a corpus shredded in some other order would not
   have it, and then these are the only way through. *)
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

(* What the join did before the grouping was noticed, kept because the grouping
   is checked rather than assumed: a corpus shredded in some other order would
   not have it, and then probing every child is the only way through. *)
let document_by_scan t id =
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

let three_hop_by_scan t org =
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

(* ---- following a key ------------------------------------------------------ *)

let grouped t = t.runs_of.valid && t.jobs_of.valid && t.steps_of.valid

(* Sum [ms] over one job's steps: a slice, addressed by the job's row. *)
let steps_ms t job_row =
  let start, len = span t.steps_of job_row in
  let d = ints t "step" "ms" in
  let acc = ref 0 in
  for i = start to start + len - 1 do
    acc := !acc + Array.unsafe_get d i
  done;
  (len, !acc)

(* Everything under one repo. The three hops now cost what the answer costs
   rather than what the corpus costs: a slice of run, a slice of job per run, a
   slice of step per job, every one an array index.

   Row-major walks the same shape. The difference left is that these rows are
   dense and contiguous where those are pointers into a heap. *)
let document t id =
  match Hashtbl.find_opt t.repo_at id with
  | None -> Workload.Missing
  | Some _ when not (grouped t) -> document_by_scan t id
  | Some row ->
      let r0, rn = span t.runs_of row in
      let jobs = ref 0 and steps = ref 0 and ms = ref 0 in
      for r = r0 to r0 + rn - 1 do
        let j0, jn = span t.jobs_of r in
        jobs := !jobs + jn;
        for j = j0 to j0 + jn - 1 do
          let n, m = steps_ms t j in
          steps := !steps + n;
          ms := !ms + m
        done
      done;
      Workload.Row (List.map string_of_int [ rn; !jobs; !steps; !ms ])

(* Three hops. The repo filter stays a scan -- there is no index on [org], and
   inventing one would be a statistic rather than a type -- but everything
   under it is a slice, so the work after the filter is proportional to what
   matched rather than to the whole corpus. *)
let three_hop t org =
  if not (grouped t) then three_hop_by_scan t org
  else begin
    let o = texts t "repo" "org" in
    let total = ref 0 in
    for i = 0 to Array.length o - 1 do
      if String.equal (Array.unsafe_get o i) org then begin
        let r0, rn = span t.runs_of i in
        for r = r0 to r0 + rn - 1 do
          let j0, jn = span t.jobs_of r in
          for j = j0 to j0 + jn - 1 do
            let _, m = steps_ms t j in
            total := !total + m
          done
        done
      end
    done;
    Workload.Sum_int !total
  end
