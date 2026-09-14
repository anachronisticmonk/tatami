(* Shred the corpus into the four tables, as COPY text.

   The work Phase 1's generated loader will eventually do. It reads the same
   file the row-major path reads, one repo at a time, and derives the two
   things the JSON does not carry: which parent an element belongs to, and what
   position it held in its array.

   COPY text rather than INSERT statements -- millions of rows is not a number
   of round trips worth making. *)

open Tatami
open Yojson.Safe.Util

let out_dir = ref "corpus/pg"
let corpus = ref "corpus/ci.json"

(* ---- COPY text format ---------------------------------------------------- *)

(* Tab separates, backslash escapes, \N is NULL. The strings hold quotes, and
   the escaping is done properly anyway: a corpus that only happens to be safe
   is a corpus that breaks when the generator changes. *)
type sink = { oc : out_channel; buf : Buffer.t; mutable rows : int }

let sink dir name =
  { oc = open_out_bin (Filename.concat dir (name ^ ".tsv"));
    buf = Buffer.create (1 lsl 20);
    rows = 0 }

let flush_sink s = Buffer.output_buffer s.oc s.buf; Buffer.clear s.buf
let close_sink s = flush_sink s; close_out s.oc

let esc s v =
  String.iter
    (fun c ->
      match c with
      | '\\' -> Buffer.add_string s.buf "\\\\"
      | '\t' -> Buffer.add_string s.buf "\\t"
      | '\n' -> Buffer.add_string s.buf "\\n"
      | '\r' -> Buffer.add_string s.buf "\\r"
      | c -> Buffer.add_char s.buf c)
    v

let sep s = Buffer.add_char s.buf '\t'

let eol s =
  Buffer.add_char s.buf '\n';
  s.rows <- s.rows + 1;
  if Buffer.length s.buf > (1 lsl 20) then flush_sink s

let wi s v = Buffer.add_string s.buf (string_of_int v)
let wf s v = Buffer.add_string s.buf (Printf.sprintf "%.17g" v)
let wb s v = Buffer.add_string s.buf (if v then "t" else "f")
let wnull s = Buffer.add_string s.buf "\\N"
let wot s = function None -> wnull s | Some v -> esc s v
let woi s = function None -> wnull s | Some v -> wi s v

(* ---- reading ------------------------------------------------------------- *)

(* An absent key and an explicit null both arrive as [`Null], which is right:
   JSON expresses optionality both ways and the schema says only that the
   column is optional. *)
let req k j = match member k j with `Null -> failwith ("missing " ^ k) | v -> v
let gs k j = to_string (req k j)
let gi k j = to_int (req k j)
let gb k j = to_bool (req k j)
let gf k j = match req k j with `Float f -> f | `Int n -> float_of_int n | _ -> failwith k
let os k j = match member k j with `String x -> Some x | _ -> None
let oi k j = match member k j with `Int x -> Some x | _ -> None
let arr k j = match member k j with `List l -> l | _ -> []

let () =
  let rec args = function
    | "--corpus" :: v :: r -> corpus := v; args r
    | "--out" :: v :: r -> out_dir := v; args r
    | [] -> ()
    | a :: _ -> prerr_endline ("unknown argument " ^ a); exit 2
  in
  args (List.tl (Array.to_list Sys.argv));
  (try Unix.mkdir !out_dir 0o755 with Unix.Unix_error _ -> ());

  let t_repo = sink !out_dir "repo" and t_run = sink !out_dir "run"
  and t_job = sink !out_dir "job" and t_step = sink !out_dir "step" in
  let t0 = Unix.gettimeofday () in

  let n =
    Corpus.iter_json !corpus ~f:(fun r ->
        let rid = gi "id" r in
        wi t_repo rid; sep t_repo; esc t_repo (gs "name" r); sep t_repo;
        esc t_repo (gs "org" r); sep t_repo; wb t_repo (gb "private" r); eol t_repo;

        List.iteri
          (fun ri u ->
            let uid = gi "id" u in
            wi t_run uid; sep t_run; wi t_run rid; sep t_run; wi t_run ri;
            sep t_run; esc t_run (gs "branch" u); sep t_run;
            esc t_run (gs "status" u); sep t_run; wi t_run (gi "ms" u);
            sep t_run; wot t_run (os "trigger" u); eol t_run;

            List.iteri
              (fun ji j ->
                let jid = gi "id" j in
                wi t_job jid; sep t_job; wi t_job uid; sep t_job; wi t_job ji;
                sep t_job; esc t_job (gs "os" j); sep t_job;
                esc t_job (gs "status" j); sep t_job; wi t_job (gi "ms" j);
                sep t_job; woi t_job (oi "exit" j); eol t_job;

                List.iteri
                  (fun si s ->
                    wi t_step (gi "id" s); sep t_step; wi t_step jid; sep t_step;
                    wi t_step si; sep t_step; esc t_step (gs "name" s);
                    sep t_step; wi t_step (gi "ms" s); sep t_step;
                    wf t_step (gf "rate" s); sep t_step;
                    wot t_step (os "error" s); eol t_step)
                  (arr "steps" j))
              (arr "jobs" u))
          (arr "runs" r))
  in
  List.iter close_sink [ t_repo; t_run; t_job; t_step ];
  Printf.eprintf "%d repos in %.1fs\n" n (Unix.gettimeofday () -. t0);
  List.iter
    (fun (name, s) -> Printf.eprintf "  %-6s %9d rows\n" name s.rows)
    [ ("repo", t_repo); ("run", t_run); ("job", t_job); ("step", t_step) ];
  Printf.eprintf "%!"
