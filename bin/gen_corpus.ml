(* The corpus: a CI service's build history, as one JSON array.

     repo                        A   a project someone is building
     `- runs      object[]       B   one build, triggered by a commit
        `- jobs   object[]       C   one machine's share of that build
           `- steps object[]     D   one command inside that job

   Four levels, three hops, every level an array. Kept deliberately small --
   nineteen fields in total -- so that a document can be read at a glance and
   a query written without consulting a schema.

   [ms] and [rate] on a step are the pair the computed query multiplies: how
   long the step ran, and what a millisecond on that runner costs. Both are
   total, so their product is known to need no validity array before a row is
   read.

   Written by hand into a buffer rather than through Yojson: at 1.5 GB the tree
   would not fit, and nothing here needs a tree.

   Nullable fields appear in both of JSON's forms, absent and explicit null,
   because Phase 1 has to infer [option] from either. *)

let usage =
  "gen_corpus [--bytes 1.5G | --rows N] [--seed N] [--out FILE]\n\
  \  --bytes  stop once the file reaches this size (K/M/G suffix)\n\
  \  --rows   stop after this many repos instead\n\
  \  --seed   same seed gives the same corpus, byte for byte\n\
  \  --out    default corpus/ci.json, - for stdout"

(* ---- a reproducible generator ------------------------------------------- *)

(* xorshift64*, written out rather than taken from Random, so the corpus does
   not change if the stdlib's generator ever does. Everything downstream reads
   this same file, so reproducibility is what keeps the stores identical. *)
let state = ref 0x2545F4914F6CDD1DL

let seed s = state := if Int64.equal s 0L then 0x2545F4914F6CDD1DL else s

let next () =
  let x = !state in
  let x = Int64.logxor x (Int64.shift_left x 13) in
  let x = Int64.logxor x (Int64.shift_right_logical x 7) in
  let x = Int64.logxor x (Int64.shift_left x 17) in
  state := x;
  Int64.mul x 0x2545F4914F6CDD1DL

let rand n =
  if n <= 0 then 0
  else Int64.to_int (Int64.rem (Int64.shift_right_logical (next ()) 1) (Int64.of_int n))

let pick a = a.(rand (Array.length a))
let chance n = rand 100 < n

(* ---- vocabulary ---------------------------------------------------------- *)

let orgs = [| "acme"; "globex"; "initech"; "hooli"; "stark" |]
let words = [| "api"; "core"; "web"; "sync"; "auth"; "edge"; "store"; "queue" |]
let branches = [| "main"; "develop"; "release" |]
let statuses = [| "ok"; "failed"; "cancelled"; "timeout" |]
let oses = [| "linux"; "macos"; "windows" |]
let triggers = [| "push"; "pr"; "schedule" |]
(* A step's duration depends on what the step is, which is both true of real
   builds and what makes an aggregate over them say something. checkout is
   always quick; test is the one that hurts. *)
let steps = [| "checkout"; "build"; "test"; "lint"; "package"; "deploy" |]
let step_lo = [|     500;    20_000;  10_000;   1_000;    5_000;    2_000 |]
let step_hi = [|   5_000;   300_000; 900_000;  30_000;   60_000;  120_000 |]

(* ---- writing ------------------------------------------------------------- *)

let buf = Buffer.create (1 lsl 22)

(* The vocabulary is alphanumeric, but error messages carry quotes on purpose:
   a reader that cannot handle an escape would otherwise pass by luck. *)
let str s =
  Buffer.add_char buf '"';
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string buf "\\\""
      | '\\' -> Buffer.add_string buf "\\\\"
      | c when Char.code c < 0x20 -> Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char buf c)
    s;
  Buffer.add_char buf '"'

let key k = str k; Buffer.add_char buf ':'
let int k v = key k; Buffer.add_string buf (string_of_int v)
let flt k v = key k; Buffer.add_string buf (Printf.sprintf "%.5g" v)
let bool k v = key k; Buffer.add_string buf (if v then "true" else "false")
let text k v = key k; str v
let comma () = Buffer.add_char buf ','

(* Half the absences are an explicit null and half are the key simply not being
   there. Both mean the same thing and both have to be inferred. *)
let null k = key k; Buffer.add_string buf "null"

let sep = ref false
let field f = if !sep then comma (); f (); sep := true

let maybe k v write =
  match v with
  | Some x -> field (fun () -> write k x)
  | None -> if chance 50 then field (fun () -> null k)

let obj f =
  let outer = !sep in
  sep := false;
  Buffer.add_char buf '{';
  f ();
  Buffer.add_char buf '}';
  sep := outer

let list k n f =
  field (fun () ->
      key k;
      Buffer.add_char buf '[';
      for i = 0 to n - 1 do
        if i > 0 then comma ();
        f i
      done;
      Buffer.add_char buf ']')

let name () = Printf.sprintf "%s-%s" (pick words) (pick words)

(* A version 4 uuid, drawn from the same generator as everything else so the
   corpus stays reproducible. Sixteen bytes, with the version and variant bits
   set as the format requires, formatted 8-4-4-4-12. *)
let uuid () =
  let b = Bytes.create 16 in
  for i = 0 to 1 do
    let x = next () in
    for j = 0 to 7 do
      Bytes.set b ((i * 8) + j)
        (Char.chr (Int64.to_int (Int64.logand (Int64.shift_right_logical x (j * 8)) 0xFFL)))
    done
  done;
  Bytes.set b 6 (Char.chr ((Char.code (Bytes.get b 6) land 0x0f) lor 0x40));
  Bytes.set b 8 (Char.chr ((Char.code (Bytes.get b 8) land 0x3f) lor 0x80));
  let h i = Printf.sprintf "%02x" (Char.code (Bytes.get b i)) in
  Printf.sprintf "%s%s%s%s-%s%s-%s%s-%s%s-%s%s%s%s%s%s" (h 0) (h 1) (h 2) (h 3)
    (h 4) (h 5) (h 6) (h 7) (h 8) (h 9) (h 10) (h 11) (h 12) (h 13) (h 14) (h 15)

(* ---- the document -------------------------------------------------------- *)

let ids = ref 0
let fresh () = incr ids; !ids

let gen_step () =
  let k = rand (Array.length steps) in
  obj (fun () ->
      field (fun () -> int "id" (fresh ()));
      field (fun () -> text "name" steps.(k));
      field (fun () -> int "ms" (step_lo.(k) + rand (step_hi.(k) - step_lo.(k))));
      field (fun () -> flt "rate" (0.0001 +. (float_of_int (rand 900) /. 1_000_000.)));
      maybe "error"
        (if chance 15 then Some (Printf.sprintf "\"%s\" not found" (name ())) else None)
        text)

let gen_job () =
  obj (fun () ->
      field (fun () -> int "id" (fresh ()));
      field (fun () -> text "os" (pick oses));
      field (fun () -> text "status" (pick statuses));
      field (fun () -> int "ms" (100 + rand 900_000));
      maybe "exit" (if chance 70 then Some (rand 128) else None) int;
      list "steps" (2 + rand 4) (fun _ -> gen_step ()))

let gen_run () =
  obj (fun () ->
      field (fun () -> int "id" (fresh ()));
      field (fun () -> text "branch" (pick branches));
      field (fun () -> text "status" (pick statuses));
      field (fun () -> int "ms" (1000 + rand 3_600_000));
      maybe "trigger" (if chance 80 then Some (pick triggers) else None) text;
      list "jobs" (1 + rand 3) (fun _ -> gen_job ()))

let gen_repo () =
  obj (fun () ->
      field (fun () -> text "id" (uuid ()));
      field (fun () -> text "name" (name ()));
      field (fun () -> text "org" (pick orgs));
      field (fun () -> bool "private" (chance 35));
      list "runs" (1 + rand 4) (fun _ -> gen_run ()))

(* ---- driver -------------------------------------------------------------- *)

let size_of_string s =
  let n = String.length s in
  if n = 0 then 0
  else
    let mult, digits =
      match s.[n - 1] with
      | 'K' | 'k' -> (1_000, String.sub s 0 (n - 1))
      | 'M' | 'm' -> (1_000_000, String.sub s 0 (n - 1))
      | 'G' | 'g' -> (1_000_000_000, String.sub s 0 (n - 1))
      | _ -> (1, s)
    in
    int_of_float (float_of_string digits *. float_of_int mult)

let () =
  let target_bytes = ref 0 and target_rows = ref 0 in
  let out = ref "corpus/ci.json" in
  let rec args = function
    | "--bytes" :: v :: rest -> target_bytes := size_of_string v; args rest
    | "--rows" :: v :: rest -> target_rows := int_of_string v; args rest
    | "--seed" :: v :: rest -> seed (Int64.of_string v); args rest
    | "--out" :: v :: rest -> out := v; args rest
    | ("-h" | "--help") :: _ -> print_endline usage; exit 0
    | [] -> ()
    | a :: _ -> prerr_endline ("unknown argument " ^ a); prerr_endline usage; exit 2
  in
  args (List.tl (Array.to_list Sys.argv));
  if !target_bytes = 0 && !target_rows = 0 then target_bytes := 64_000_000;

  let oc =
    if !out = "-" then stdout
    else (
      (try Unix.mkdir (Filename.dirname !out) 0o755 with Unix.Unix_error _ -> ());
      open_out_bin !out)
  in
  let written = ref 0 in
  let flush_buf () =
    written := !written + Buffer.length buf;
    Buffer.output_buffer oc buf;
    Buffer.clear buf
  in
  let t0 = Unix.gettimeofday () in
  Buffer.add_char buf '[';
  let repos = ref 0 in
  let more () =
    if !target_rows > 0 then !repos < !target_rows
    else !written + Buffer.length buf < !target_bytes
  in
  while more () do
    if !repos > 0 then comma ();
    sep := false;
    gen_repo ();
    incr repos;
    if Buffer.length buf > (1 lsl 21) then flush_buf ()
  done;
  Buffer.add_char buf ']';
  Buffer.add_char buf '\n';
  flush_buf ();
  if !out <> "-" then close_out oc;
  Printf.eprintf "%d repos, %d objects, %.2f GB, %.1fs\n%!" !repos !ids
    (float_of_int !written /. 1e9)
    (Unix.gettimeofday () -. t0)
