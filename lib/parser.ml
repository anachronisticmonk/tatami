(*tokens in Query.t out*)

exception Error of string

let fail fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt

(* skip the keyword *)
let keyword w = function
  | Lexer.Word x :: rest when x = w -> rest
  | t :: _ -> fail "expected %s, found %s" w (Lexer.to_string t)
  | [] -> fail "expected %s, found nothing" w

let name = function
  | Lexer.Word w :: rest -> (w, rest)
  | t :: _ -> fail "expected a name, found %s" (Lexer.to_string t)
  | [] -> fail "expected a name, found nothing"

let comparison = function
  | Lexer.Punct "=" :: rest -> (Query.Eq, rest)
  | Lexer.Punct "<>" :: rest -> (Query.Ne, rest)
  | Lexer.Punct "<" :: rest -> (Query.Lt, rest)
  | Lexer.Punct "<=" :: rest -> (Query.Le, rest)
  | Lexer.Punct ">" :: rest -> (Query.Gt, rest)
  | Lexer.Punct ">=" :: rest -> (Query.Ge, rest)
  | t :: _ -> fail "expected a comparison, found %s" (Lexer.to_string t)
  | [] -> fail "expected a comparison, found nothing"

(* The dot is what decides int or float *)
(* NOTE so that literal [Num "4"] -> Query.Int 4 *)
let literal = function
  | Lexer.Num n :: rest ->
    let v =
      if String.contains n '.' then Query.Float (float_of_string n)
      else Query.Int (int_of_string n)
          in
          (v,rest)
  | Lexer.Str s :: rest -> (Query.Text s, rest)
  | t :: _ -> fail "expected a value, found %s" (Lexer.to_string t)
  | [] -> fail "expected a value, found nothing"

(* select a,b,c from T this helper collects ["a";"b";"c"] *)
let rec columns toks =
  let c, rest = name toks in
  match rest with
  | Lexer.Punct "," :: more -> let cs, rest = columns more in
    (c :: cs, rest)
  | _ -> ([c], rest)

let select_list = function
  | Lexer.Punct "*" :: rest -> ([], rest)
  | toks -> columns toks

let predicate toks =
  let column, rest = name toks in
  let op, rest = comparison rest in
  let value, rest = literal rest in
  ({Query.column; op; value}, rest)


(* the whole purpose of the function was to do the following *)
(* parse "select qty from orders where qty > 4" *)
(* becomes a record of {table = "orderes"; select = ["qty"]; where Some *)
(* {colunm = qty; op = Gt value = Int 4} } *)
(* NOTE we are doing this because the analysis can't read a string *)
(* it needs a value it can inspect - which column, what type is it nullable? *)
(* we are constructing the query *)


let parse text =
  let rest = keyword "select" (Lexer.tokenise text) in
  let select, rest = select_list rest in
  let rest = keyword "from" rest in
  let table, rest = name rest in
  let where, rest =
    match rest with
    | Lexer.Word "where" :: more ->
      let p, rest = predicate more in
      (Some p, rest)
    | _ -> (None, rest)
 in
 match rest with
 | [ Lexer.End ] | [] -> { Query.table; select; where }
 | t :: _ -> fail "unexpected %s at the end of the query" (Lexer.to_string t)
