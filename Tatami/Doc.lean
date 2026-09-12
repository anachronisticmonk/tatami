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

mutual

/-- A size for a document: an object or an array is strictly larger than
    anything inside it. Its only purpose is the termination argument for the
    walk in `Tatami.Infer`, which recurses into a member of an object and so
    is not structural. -/
def Doc.size : Doc → Nat
  | .null => 1
  | .bool _ => 1
  | .num _ => 1
  | .str _ => 1
  | .arr els => 1 + Doc.sizeList els
  | .obj ms => 1 + Doc.sizeVals ms

def Doc.sizeList : List Doc → Nat
  | [] => 0
  | d :: tl => Doc.size d + Doc.sizeList tl

def Doc.sizeVals : List (String × Doc) → Nat
  | [] => 0
  | m :: tl => Doc.size m.2 + Doc.sizeVals tl

end

/-- Every document has positive size, which is what makes dropping one member
    from a list a strict decrease. -/
theorem Doc.size_pos (d : Doc) : 0 < d.size := by
  cases d <;> simp [Doc.size] <;> omega

/-- Dropping one element from a list is a strict decrease, because every
    document has positive size. The walk in `Tatami.Infer` needs both of
    these in scope at its recursive calls. -/
theorem Doc.sizeList_lt (d : Doc) (tl : List Doc) :
    Doc.sizeList tl < Doc.sizeList (d :: tl) := by
  show Doc.sizeList tl < Doc.size d + Doc.sizeList tl
  have := Doc.size_pos d
  omega

theorem Doc.sizeVals_lt (m : String × Doc) (tl : List (String × Doc)) :
    Doc.sizeVals tl < Doc.sizeVals (m :: tl) := by
  show Doc.sizeVals tl < Doc.size m.2 + Doc.sizeVals tl
  have := Doc.size_pos m.2
  omega

/-- A member's value is smaller than the list it sits in, and so is whatever
    that value contains. One lemma per recursive call in `Tatami.Infer`; each
    is `omega` once the size of the constructor is unfolded, which is why they
    are stated here rather than left to the termination checker. -/
theorem Doc.size_lt_cons (k : String) (v : Doc) (tl : List (String × Doc)) :
    v.size < 1 + Doc.sizeVals ((k, v) :: tl) := by
  show v.size < 1 + (Doc.size v + Doc.sizeVals tl)
  omega

theorem Doc.size_lt_consList (e : Doc) (tl : List Doc) :
    e.size < 1 + Doc.sizeList (e :: tl) := by
  show e.size < 1 + (Doc.size e + Doc.sizeList tl)
  omega

theorem Doc.sizeVals_lt_obj (k : String) (entries tl : List (String × Doc)) :
    Doc.sizeVals entries < Doc.sizeVals ((k, Doc.obj entries) :: tl) := by
  show Doc.sizeVals entries < (1 + Doc.sizeVals entries) + Doc.sizeVals tl
  omega

theorem Doc.sizeList_lt_arr (k : String) (els : List Doc) (tl : List (String × Doc)) :
    Doc.sizeList els < Doc.sizeVals ((k, Doc.arr els) :: tl) := by
  show Doc.sizeList els < (1 + Doc.sizeList els) + Doc.sizeVals tl
  omega

end Tatami
