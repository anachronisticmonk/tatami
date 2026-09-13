(* The corpus: CI build telemetry as one large JSON array.

   Shape, and why this one. Every level is an array, which is the case the Lean
   model handles with [coll] and which the first attempt never exercised. One
   nested object as well, so [ref] appears too.

     repository                          A
     |- owner            object          ref:  its own table, parent holds a key
     |- topics           string[]        coll: scalar array, its own table
     `- runs             object[]        B
        `- jobs          object[]        C
           |- labels     string[]        coll: scalar array
           `- steps      object[]        D

   repository -> runs -> jobs -> steps is three hops. Seven tables once shredded.

   Written by hand into a buffer rather than through Yojson: at this size the
   tree would not fit in memory, and nothing here needs a tree. The reader is
   free to use Yojson -- that is the baseline being measured.

   Nullable fields appear in both of JSON's two forms, absent and explicit
   null, because Phase 1 must infer [option] from either. Roughly half each. *)

let usage =
  "gen_corpus [--bytes 1.5G | --rows N] [--seed N] [--out FILE]\n\
  \  --bytes  stop once the file reaches this size (K/M/G suffix)\n\
  \  --rows   stop after this many repositories instead\n\
  \  --seed   same seed gives the same corpus, byte for byte\n\
  \  --out    default corpus/ci.json, - for stdout"

(* ---- a reproducible generator ------------------------------------------- *)

(* xorshift64*, written out rather than taken from Random, so the corpus does
   not change if the stdlib's generator ever does. The Postgres loader reads
   this same file, so reproducibility is what keeps the two stores identical. *)
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

let orgs = [| "acme"; "globex"; "initech"; "umbrella"; "hooli"; "soylent"; "stark" |]
let words = [| "api"; "core"; "web"; "sync"; "auth"; "batch"; "edge"; "store"; "index";
               "queue"; "proxy"; "render"; "parse"; "graph"; "shard" |]
let branches = [| "main"; "develop"; "release"; "hotfix"; "staging" |]
let statuses = [| "success"; "failure"; "cancelled"; "timed_out"; "skipped" |]
let oses = [| "ubuntu-22.04"; "ubuntu-20.04"; "macos-14"; "windows-2022" |]
let triggers = [| "push"; "pull_request"; "schedule"; "workflow_dispatch" |]
let step_names = [| "checkout"; "setup"; "restore-cache"; "install"; "build"; "unit-test";
                    "integration-test"; "lint"; "typecheck"; "package"; "upload"; "deploy" |]
let topics = [| "ocaml"; "rust"; "database"; "compiler"; "cli"; "web"; "async";
                "distributed"; "parser"; "gpu"; "columnar"; "json" |]
let label_pool = [| "self-hosted"; "gpu"; "large"; "spot"; "arm64"; "x64"; "isolated" |]

let hex = "0123456789abcdef"

(* ---- writing ------------------------------------------------------------- *)

let buf = Buffer.create (1 lsl 22)

(* Our vocabulary is alphanumeric, but error messages carry quotes on purpose:
   a reader that cannot handle an escape would otherwise pass by luck. *)
let str s =
  Buffer.add_char buf '"';
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string buf "\\\""
      | '\\' -> Buffer.add_string buf "\\\\"
      | '\n' -> Buffer.add_string buf "\\n"
      | c when Char.code c < 0x20 -> Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char buf c)
    s;
  Buffer.add_char buf '"'

let key k = str k; Buffer.add_char buf ':'
let int k v = key k; Buffer.add_string buf (string_of_int v)
let flt k v = key k; Buffer.add_string buf (Printf.sprintf "%.6g" v)
let bool k v = key k; Buffer.add_string buf (if v then "true" else "false")
let text k v = key k; str v
let comma () = Buffer.add_char buf ','

(* A nullable field in both of JSON's forms. [absent] omits the key entirely,
   which is the harder case for inference and the more common one in practice. *)
let opt_text k = function
  | None -> if chance 50 then (key k; Buffer.add_string buf "null") else ()
  | Some v -> text k v

let opt_int k = function
  | None -> if chance 50 then (key k; Buffer.add_string buf "null") else ()
  | Some v -> int k v

(* [sep] tracks whether a comma is needed, since an omitted nullable key must
   not leave a dangling one. *)
let field sep f = if !sep then comma (); f (); sep := true
let maybe sep f =
  let before = Buffer.length buf in
  if !sep then comma ();
  let after_comma = Buffer.length buf in
  f ();
  if Buffer.length buf = after_comma then Buffer.truncate buf before else sep := true

let sha () =
  let b = Bytes.create 40 in
  for i = 0 to 39 do Bytes.set b i hex.[rand 16] done;
  Bytes.to_string b

let name () = Printf.sprintf "%s-%s" (pick words) (pick words)

(* ---- the document -------------------------------------------------------- *)

let ids = ref 0
let fresh () = incr ids; !ids

let gen_step () =
  let s = ref false in
  Buffer.add_char buf '{';
  field s (fun () -> int "id" (fresh ()));
  field s (fun () -> text "name" (pick step_names));
  field s (fun () -> text "status" (pick statuses));
  field s (fun () -> int "duration_ms" (1 + rand 60_000));
  (* the float the computed-column query multiplies by *)
  field s (fun () -> flt "cost_per_ms" (0.00001 +. (float_of_int (rand 400) /. 1_000_000.)));
  field s (fun () -> int "log_bytes" (rand 2_000_000));
  field s (fun () -> int "memory_mb" (64 + rand 8000));
  maybe s (fun () ->
      opt_text "error"
        (if chance 18 then
           Some (Printf.sprintf "exit %d: \"%s\" not found" (1 + rand 125) (name ()))
         else None));
  Buffer.add_char buf '}'

let gen_job () =
  let s = ref false in
  Buffer.add_char buf '{';
  field s (fun () -> int "id" (fresh ()));
  field s (fun () -> text "name" (name ()));
  field s (fun () -> text "runner_os" (pick oses));
  field s (fun () -> text "status" (pick statuses));
  field s (fun () -> int "duration_ms" (100 + rand 900_000));
  field s (fun () -> int "queued_ms" (rand 120_000));
  maybe s (fun () -> opt_int "exit_code" (if chance 70 then Some (rand 128) else None));
  field s (fun () ->
      key "labels";
      Buffer.add_char buf '[';
      let n = rand 4 in
      for i = 0 to n - 1 do
        if i > 0 then comma ();
        str (pick label_pool)
      done;
      Buffer.add_char buf ']');
  field s (fun () ->
      key "steps";
      Buffer.add_char buf '[';
      let n = 3 + rand 6 in
      for i = 0 to n - 1 do
        if i > 0 then comma ();
        gen_step ()
      done;
      Buffer.add_char buf ']');
  Buffer.add_char buf '}'

let gen_run () =
  let s = ref false in
  Buffer.add_char buf '{';
  field s (fun () -> int "id" (fresh ()));
  field s (fun () -> int "number" (1 + rand 5000));
  field s (fun () -> text "commit_sha" (sha ()));
  field s (fun () -> text "branch" (pick branches));
  field s (fun () -> text "status" (pick statuses));
  field s (fun () -> int "started_at" (1_600_000_000 + rand 200_000_000));
  field s (fun () -> int "duration_ms" (1000 + rand 3_600_000));
  maybe s (fun () -> opt_text "trigger" (if chance 80 then Some (pick triggers) else None));
  field s (fun () ->
      key "jobs";
      Buffer.add_char buf '[';
      let n = 1 + rand 4 in
      for i = 0 to n - 1 do
        if i > 0 then comma ();
        gen_job ()
      done;
      Buffer.add_char buf ']');
  Buffer.add_char buf '}'

let gen_owner () =
  let s = ref false in
  Buffer.add_char buf '{';
  field s (fun () -> int "id" (fresh ()));
  field s (fun () -> text "login" (pick orgs ^ string_of_int (rand 900)));
  field s (fun () -> text "kind" (if chance 30 then "user" else "org"));
  field s (fun () -> int "followers" (rand 50_000));
  maybe s (fun () ->
      opt_text "email"
        (if chance 60 then Some (Printf.sprintf "%s@%s.example" (pick words) (pick orgs))
         else None));
  Buffer.add_char buf '}'

let gen_repository () =
  let s = ref false in
  Buffer.add_char buf '{';
  field s (fun () -> int "id" (fresh ()));
  field s (fun () -> text "name" (name ()));
  field s (fun () -> text "org" (pick orgs));
  field s (fun () -> text "default_branch" (pick branches));
  field s (fun () -> bool "is_private" (chance 35));
  field s (fun () -> int "stars" (rand 40_000));
  field s (fun () -> int "created_at" (1_400_000_000 + rand 300_000_000));
  maybe s (fun () ->
      opt_text "description"
        (if chance 75 then Some (Printf.sprintf "%s for %s" (name ()) (pick orgs)) else None));
  field s (fun () -> key "owner"; gen_owner ());
  field s (fun () ->
      key "topics";
      Buffer.add_char buf '[';
      let n = rand 6 in
      for i = 0 to n - 1 do
        if i > 0 then comma ();
        str (pick topics)
      done;
      Buffer.add_char buf ']');
  field s (fun () ->
      key "runs";
      Buffer.add_char buf '[';
      let n = 1 + rand 6 in
      for i = 0 to n - 1 do
        if i > 0 then comma ();
        gen_run ()
      done;
      Buffer.add_char buf ']');
  Buffer.add_char buf '}'

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

  let oc = if !out = "-" then stdout else (
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
  let continue_ () =
    if !target_rows > 0 then !repos < !target_rows
    else !written + Buffer.length buf < !target_bytes
  in
  while continue_ () do
    if !repos > 0 then comma ();
    gen_repository ();
    incr repos;
    if Buffer.length buf > (1 lsl 21) then flush_buf ()
  done;
  Buffer.add_char buf ']';
  Buffer.add_char buf '\n';
  flush_buf ();
  if !out <> "-" then close_out oc;
  let dt = Unix.gettimeofday () -. t0 in
  Printf.eprintf "%d repositories, %d objects, %.2f GB, %.1fs\n%!" !repos !ids
    (float_of_int !written /. 1e9) dt
