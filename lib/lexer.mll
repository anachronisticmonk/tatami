{
type token =
  | Word of string (* an identifier or a keyword, folded to lower case *)
  | Num of string (* kept as text; int or float is the parser's decision *)
  | Str of string (* the contents of a 'literal', unquoted *)
  | Punct of string
  | End

exception Error of string

let fail fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt

(* Where a string literal is assembled. It cannot be a substring of the input,
   because '' collapses to a single quote. *)
let buf = Buffer.create 32

let to_string = function
  | Word w -> w
  | Num n -> n
  | Str s -> "'" ^ s ^ "'"
  | Punct p -> p
  | End -> "end of query"
}

let space = [' ' '\t' '\n' '\r']
let digit = ['0'-'9']
let word  = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let num   = '-'? digit+ ('.' digit+)?

(* Longest match wins, and ties go to the earlier rule -- which is why "<="
   sits above '<' and needs no lookahead of its own. *)
rule token = parse
  | space+                        { token lexbuf }
  | num as n                      { Num n }
  | word as w                     { Word (String.lowercase_ascii w) }
  | "<=" | ">=" | "<>"     as p   { Punct p }
  | "!="                          { Punct "<>" }
  | [',' '*' '=' '<' '>']  as c   { Punct (String.make 1 c) }
  | '\''                          { Buffer.clear buf; quoted lexbuf }
  | eof                           { End }
  | _ as c                        { fail "unexpected character %C" c }

(* A second mode. Inside a literal every character is content until a quote,
   so the ordinary rules do not apply and we switch here until it closes. *)
and quoted = parse
  | "''"     { Buffer.add_char buf '\''; quoted lexbuf }
  | '\''     { Str (Buffer.contents buf) }
  | eof      { fail "unterminated string literal" }
  | _ as c   { Buffer.add_char buf c; quoted lexbuf }

{
(* Every token in a string, ending with [End]. The parser wants a list rather
   than a lexbuf: the grammar is small enough to look ahead by pattern
   matching, which reads better than threading a cursor. *)
let tokenise (s : string) : token list =
  let lb = Lexing.from_string s in
  let rec go acc =
    match token lb with
    | End -> List.rev (End :: acc)
    | t -> go (t :: acc)
  in
  go []
}
