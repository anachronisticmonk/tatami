namespace Tatami

/-- A JSON document, as written.

    `Lean.Json` parses an object into a tree map, which silently discards a
    repeated member and loses the order of the rest. It also normalises
    numbers, so the text a number was written with is not recoverable. Both
    matter here, so we read JSON ourselves.

    Keeping objects as association lists has a second benefit: `Doc` is an
    ordinary inductive type, so a walk over it can be given a termination
    argument, which a walk over a tree map cannot. -/
inductive Doc where
  | null
  | bool : Bool → Doc
  | num  : String → Doc                  -- the literal exactly as written
  | str  : String → Doc
  | arr  : List Doc → Doc
  | obj  : List (String × Doc) → Doc     -- in order, repeats kept
  deriving Repr, Inhabited

namespace Doc

abbrev Input := List Char

private def isWs (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\t' || c == '\r'

private def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def skipWs : Input → Input
  | c :: rest => if isWs c then skipWs rest else c :: rest
  | [] => []

private def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

private def pStringBody (acc : String) : Input → Except String (String × Input)
  | '"' :: rest => .ok (acc, rest)
  | '\\' :: 'u' :: a :: b :: c :: d :: rest =>
      match hexVal a, hexVal b, hexVal c, hexVal d with
      | some x, some y, some z, some w =>
          pStringBody (acc.push (Char.ofNat (((x * 16 + y) * 16 + z) * 16 + w))) rest
      | _, _, _, _ => .error "malformed \\u escape"
  | '\\' :: e :: rest =>
      let c :=
        if e == 'n' then '\n' else if e == 't' then '\t'
        else if e == 'r' then '\r' else if e == 'b' then Char.ofNat 8
        else if e == 'f' then Char.ofNat 12 else e
      pStringBody (acc.push c) rest
  | c :: rest => pStringBody (acc.push c) rest
  | [] => .error "unterminated string"

private def pString : Input → Except String (String × Input)
  | '"' :: rest => pStringBody "" rest
  | _ => .error "expected a string"

private def pDigits (acc : String) : Input → String × Input
  | c :: rest => if isDigit c then pDigits (acc.push c) rest else (acc, c :: rest)
  | [] => (acc, [])

/-- A number, kept as the text it was written with, so that `1` and `1.0`
    remain distinguishable. -/
private def pNumber (s : Input) : Except String (Doc × Input) :=
  let (sign, s) := match s with | '-' :: r => ("-", r) | _ => ("", s)
  let (intPart, s) := pDigits "" s
  if intPart.isEmpty then .error "expected a number" else
  let (frac, s) :=
    match s with
    | '.' :: r => let (d, r) := pDigits "" r; ("." ++ d, r)
    | _ => ("", s)
  let (exp, s) :=
    match s with
    | e :: r =>
        if e == 'e' || e == 'E' then
          let (sgn, r) := match r with
            | '+' :: r' => ("+", r') | '-' :: r' => ("-", r') | _ => ("", r)
          let (d, r) := pDigits "" r
          (String.singleton e ++ sgn ++ d, r)
        else ("", e :: r)
    | [] => ("", s)
  .ok (.num (sign ++ intPart ++ frac ++ exp), s)

/-- The value parser. Marked `partial`: the input shrinks at every step, but
    saying so to Lean would require carrying the proof through the return
    type. Like the printer, the reader is a trusted boundary. -/
private partial def pValue (s : Input) : Except String (Doc × Input) := do
  match skipWs s with
  | '{' :: r => pObject [] (skipWs r)
  | '[' :: r => pArray [] (skipWs r)
  | '"' :: r => let (v, r) ← pStringBody "" r; return (.str v, r)
  | 't' :: 'r' :: 'u' :: 'e' :: r => return (.bool true, r)
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: r => return (.bool false, r)
  | 'n' :: 'u' :: 'l' :: 'l' :: r => return (.null, r)
  | t@('-' :: _) => pNumber t
  | t@(c :: _) => if isDigit c then pNumber t else .error s!"unexpected character '{c}'"
  | [] => .error "unexpected end of input"

  where
    pObject (acc : List (String × Doc)) : Input → Except String (Doc × Input)
      | '}' :: r => .ok (.obj acc.reverse, r)
      | s => do
          let (k, s) ← pString (skipWs s)
          match skipWs s with
          | ':' :: s =>
              let (v, s) ← pValue s
              match skipWs s with
              | ',' :: s => pObject ((k, v) :: acc) (skipWs s)
              | '}' :: s => .ok (.obj ((k, v) :: acc).reverse, s)
              | _ => .error "expected ',' or '}'"
          | _ => .error "expected ':'"

    pArray (acc : List Doc) : Input → Except String (Doc × Input)
      | ']' :: r => .ok (.arr acc.reverse, r)
      | s => do
          let (v, s) ← pValue s
          match skipWs s with
          | ',' :: s => pArray (v :: acc) (skipWs s)
          | ']' :: s => .ok (.arr (v :: acc).reverse, s)
          | _ => .error "expected ',' or ']'"

def parse (text : String) : Except String Doc := do
  let (v, rest) ← pValue text.toList
  match skipWs rest with
  | [] => return v
  | _ => .error "trailing content after the document"

def describe : Doc → String
  | .null => "null"
  | .bool _ => "a boolean"
  | .num _ => "a number"
  | .str _ => "a string"
  | .arr _ => "an array"
  | .obj _ => "an object"

end Doc
end Tatami
