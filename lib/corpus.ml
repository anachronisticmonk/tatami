(* Reading a JSON array that does not fit in memory.

   The corpus is one array of 159,388 repositories, 1.5 GB. Handing that to
   [Yojson.Safe.from_file] would build a tree several times the size of the
   file and is not an option, so the array is split here and each element is
   parsed on its own -- one repository at a time, about 9 KB live.

   This is not a JSON parser. It finds the boundaries between top-level
   elements and nothing else, which needs only a brace depth and enough of a
   string state machine to know that a brace inside a quoted string is not a
   brace. Whoever gets the element decides how to parse it, which is the point:
   the row-major path hands it to Yojson and the columnar path shreds it. *)

let chunk_size = 1 lsl 20

type reader = {
  ic : in_channel;
  buf : Bytes.t;
  mutable len : int;
  mutable pos : int;
}

let refill r =
  r.len <- input r.ic r.buf 0 chunk_size;
  r.pos <- 0;
  r.len > 0

let rec peek r =
  if r.pos < r.len then Some (Bytes.unsafe_get r.buf r.pos)
  else if refill r then peek r
  else None

let skip r = r.pos <- r.pos + 1

let rec skip_while r p =
  match peek r with Some c when p c -> skip r; skip_while r p | _ -> ()

let is_space c = c = ' ' || c = '\n' || c = '\r' || c = '\t'

(* One element, copied out with its structure intact. Depth counts braces and
   brackets together -- an element may be an object or an array and we do not
   care which -- and the string state machine exists because [error] messages
   carry quotes, and could carry a brace. *)
let element r out =
  Buffer.clear out;
  let depth = ref 0 and instr = ref false and esc = ref false in
  let fin = ref false in
  while not !fin do
    match peek r with
    | None -> fin := true
    | Some c ->
        Buffer.add_char out c;
        skip r;
        if !esc then esc := false
        else if !instr then (
          if c = '\\' then esc := true else if c = '"' then instr := false)
        else if c = '"' then instr := true
        else if c = '{' || c = '[' then incr depth
        else if c = '}' || c = ']' then (
          decr depth;
          if !depth = 0 then fin := true)
  done;
  Buffer.length out > 0

(* [f] is called once per element, with a buffer that is reused -- so the
   callback must consume it rather than keep it. *)
let iter path ~f =
  let r = { ic = open_in_bin path; buf = Bytes.create chunk_size; len = 0; pos = 0 } in
  Fun.protect
    ~finally:(fun () -> close_in r.ic)
    (fun () ->
      skip_while r is_space;
      (match peek r with
      | Some '[' -> skip r
      | Some c -> failwith (Printf.sprintf "%s: expected '[', found %C" path c)
      | None -> failwith (path ^ ": empty"));
      let out = Buffer.create (1 lsl 16) in
      let fin = ref false in
      let n = ref 0 in
      while not !fin do
        skip_while r (fun c -> is_space c || c = ',');
        match peek r with
        | None | Some ']' -> fin := true
        | Some _ ->
            if element r out then (
              incr n;
              f out)
            else fin := true
      done;
      !n)

(* Every element, as a Yojson value. The convenience the row-major baseline
   uses; the columnar loader uses [iter] directly. *)
let iter_json path ~f =
  iter path ~f:(fun b -> f (Yojson.Safe.from_string (Buffer.contents b)))
