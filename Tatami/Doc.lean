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

/-- The optional leading sign. -/
private def pSign : Input → String × Input
  | '-' :: r => ("-", r)
  | s => ("", s)

/-- The optional fractional part. -/
private def pFrac : Input → String × Input
  | '.' :: r => let (d, r) := pDigits "" r; ("." ++ d, r)
  | s => ("", s)

/-- The optional sign of an exponent. -/
private def pExpSign : Input → String × Input
  | '+' :: r => ("+", r)
  | '-' :: r => ("-", r)
  | s => ("", s)

/-- The optional exponent. -/
private def pExp : Input → String × Input
  | e :: r =>
      if e == 'e' || e == 'E' then
        let (sgn, r1) := pExpSign r
        let (d, r2) := pDigits "" r1
        (String.singleton e ++ sgn ++ d, r2)
      else ("", e :: r)
  | [] => ("", [])

/-- A number, kept as the text it was written with, so that `1` and `1.0`
    remain distinguishable. Split into its four parts so that each can be
    given its own lemma below. -/
private def pNumber (s : Input) : Except String (Doc × Input) :=
  let (sign, s1) := pSign s
  let (intPart, s2) := pDigits "" s1
  if intPart.isEmpty then .error "expected a number" else
  let (frac, s3) := pFrac s2
  let (exp, s4) := pExp s3
  .ok (.num (sign ++ intPart ++ frac ++ exp), s4)

/-! ### Termination

    `pValue` recurses through `pObject` and `pArray` on input that comes back
    from a helper, so Lean cannot see that it shrinks. The lemmas below say so
    once each, and `decreasing_by` at the end of the file does nothing but
    invoke them -- the parser itself stays as it reads. -/

private theorem skipWs_le : ∀ s : Input, (skipWs s).length ≤ s.length
  | [] => by simp [skipWs]
  | c :: rest => by
      simp only [skipWs]
      split
      · exact Nat.le_succ_of_le (skipWs_le rest)
      · simp

private theorem pDigits_le : ∀ (acc : String) (s : Input), (pDigits acc s).2.length ≤ s.length
  | _, [] => by simp [pDigits]
  | acc, c :: rest => by
      simp only [pDigits]
      split
      · exact Nat.le_succ_of_le (pDigits_le _ rest)
      · simp

private theorem pStringBody_lt (acc : String) (s : Input) (v : String) (r : Input)
    (h : pStringBody acc s = .ok (v, r)) : r.length < s.length := by
  fun_induction pStringBody acc s <;> simp_all <;> omega

private theorem pString_lt (s : Input) (k : String) (r : Input)
    (h : pString s = .ok (k, r)) : r.length < s.length := by
  unfold pString at h
  split at h
  · exact Nat.lt_succ_of_lt (pStringBody_lt _ _ _ _ h)
  · simp at h

/-- A run of digits consumes at least the first character, when it is one. -/
private theorem pDigits_lt (acc : String) (c : Char) (rest : Input) (h : isDigit c) :
    (pDigits acc (c :: rest)).2.length < (c :: rest).length := by
  simp only [pDigits, h, if_pos]
  exact Nat.lt_succ_of_le (pDigits_le _ rest)

private theorem pSign_le : ∀ s : Input, (pSign s).2.length ≤ s.length
  | [] => by simp [pSign]
  | _ :: _ => by simp only [pSign]; split <;> simp_all

private theorem pExpSign_le : ∀ s : Input, (pExpSign s).2.length ≤ s.length
  | [] => by simp [pExpSign]
  | _ :: _ => by simp only [pExpSign]; split <;> simp_all

private theorem pFrac_le : ∀ s : Input, (pFrac s).2.length ≤ s.length
  | [] => by simp [pFrac]
  | c :: r => by
      simp only [pFrac]
      split
      · have := pDigits_le "" r
        simp_all
        omega
      · simp

private theorem pExp_le : ∀ s : Input, (pExp s).2.length ≤ s.length
  | [] => by simp [pExp]
  | e :: r => by
      simp only [pExp]
      split
      · have h1 := pExpSign_le r
        have h2 := pDigits_le "" (pExpSign r).2
        simp
        omega
      · simp

/-- A run of digits that produced something consumed something. -/
private theorem pDigits_shrinks (acc : String) (s : Input)
    (h : (pDigits acc s).1 ≠ acc) : (pDigits acc s).2.length < s.length := by
  match s with
  | [] => simp [pDigits] at h
  | c :: rest =>
      by_cases hc : isDigit c
      · exact pDigits_lt acc c rest hc
      · simp [pDigits, hc] at h

/-- A number always consumes at least its first digit. -/
private theorem pNumber_lt (s : Input) (d : Doc) (r : Input)
    (h : pNumber s = .ok (d, r)) : r.length < s.length := by
  unfold pNumber at h
  split at h                          -- peel the sign
  rename_i sgn s1 hsign
  split at h                          -- peel the integer digits
  rename_i ipart s2 hdig
  split at h                          -- they must not be empty
  · simp at h                         -- ...or this is an error, not an ok
  · rename_i hne
    injection h with h
    injection h with _ h
    subst h
    have h1 : s1.length ≤ s.length := by
      have := pSign_le s; rw [hsign] at this; simpa using this
    have h2 : s2.length < s1.length := by
      have := pDigits_shrinks "" s1 (by rw [hdig]; simpa using hne)
      rw [hdig] at this; simpa using this
    have h3 := pFrac_le s2
    have h4 := pExp_le (pFrac s2).2
    show (pExp (pFrac s2).2).2.length < s.length
    omega

/-- What a parser hands back: a value, the input left over, and the fact that
    the leftover is shorter than what went in.

    That last part has to be in the type. `pObject` recurses on whatever
    `pValue` gives back, so its termination depends on a property of
    `pValue` -- the function being defined. There is no lemma to prove
    beforehand, because the function does not exist yet; it has to be proved
    at the same time as the definition.

    The proof is a `Prop`, so it is erased at compile time. It costs nothing
    at runtime: the generated code is the same recursion either way. -/
private abbrev Parsed (s : Input) := { p : Doc × Input // p.2.length < s.length }

mutual

/-- One JSON value. The first non-blank character says which kind. -/
private def pValue (s : Input) : Except String (Parsed s) :=
  match hs : skipWs s with
  | '{' :: r =>
      match pObject [] (skipWs r) with
      | .error e => .error e
      | .ok ⟨p, hp⟩ => .ok ⟨p, by
          have a := skipWs_le s; rw [hs] at a; simp at a
          have b := skipWs_le r
          omega⟩
  | '[' :: r =>
      match pArray [] (skipWs r) with
      | .error e => .error e
      | .ok ⟨p, hp⟩ => .ok ⟨p, by
          have a := skipWs_le s; rw [hs] at a; simp at a
          have b := skipWs_le r
          omega⟩
  | '"' :: r =>
      match hb : pStringBody "" r with
      | .error e => .error e
      | .ok (v, r') => .ok ⟨(.str v, r'), by
          show r'.length < s.length
          have a := skipWs_le s; rw [hs] at a; simp at a
          have b := pStringBody_lt "" r v r' hb
          omega⟩
  | 't' :: 'r' :: 'u' :: 'e' :: r => .ok ⟨(.bool true, r), by
      show r.length < s.length
      have a := skipWs_le s; rw [hs] at a; simp at a; omega⟩
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: r => .ok ⟨(.bool false, r), by
      show r.length < s.length
      have a := skipWs_le s; rw [hs] at a; simp at a; omega⟩
  | 'n' :: 'u' :: 'l' :: 'l' :: r => .ok ⟨(.null, r), by
      show r.length < s.length
      have a := skipWs_le s; rw [hs] at a; simp at a; omega⟩
  | '-' :: tail =>
      match hn : pNumber ('-' :: tail) with
      | .error e => .error e
      | .ok (d, r) => .ok ⟨(d, r), by
          show r.length < s.length
          have a := skipWs_le s; rw [hs] at a
          have b := pNumber_lt ('-' :: tail) d r hn
          simp at a b
          omega⟩
  | c :: tail =>
      if isDigit c then
        match hn : pNumber (c :: tail) with
        | .error e => .error e
        | .ok (d, r) => .ok ⟨(d, r), by
            show r.length < s.length
            have a := skipWs_le s; rw [hs] at a
            have b := pNumber_lt (c :: tail) d r hn
            simp at a b
            omega⟩
      else .error s!"unexpected character '{c}'"
  | [] => .error "unexpected end of input"
-- The measure is (input length, who). `pArray` hands the *same* input to
-- `pValue`, so length alone cannot decrease; ranking `pValue` below the other
-- two makes that step count as progress, and every other call shortens the
-- input outright.
termination_by (s.length, 0)
decreasing_by
  all_goals
    have a := skipWs_le s
    rw [hs] at a
    simp at a
    have b := skipWs_le r
    omega

/-- The members of an object, after the opening brace.

    The fallback branch names its input `rest` rather than reusing `s`: the
    return type mentions `s`, so matching on it abstracts it, and the goals
    are then about the matched form. -/
private def pObject (acc : List (String × Doc)) (s : Input) : Except String (Parsed s) :=
  match s with
  | '}' :: r => .ok ⟨(.obj acc.reverse, r), by simp⟩
  | rest =>
    match hk : pString (skipWs rest) with
    | .error e => .error e
    | .ok (k, s1) =>
      match hc : skipWs s1 with
      | ':' :: s2 =>
        match pValue s2 with
        | .error e => .error e
        | .ok ⟨(v, s3), h3⟩ =>
          match hcm : skipWs s3 with
          | ',' :: s4 =>
            match pObject ((k, v) :: acc) (skipWs s4) with
            | .error e => .error e
            | .ok ⟨p, hp⟩ => .ok ⟨p, by
                simp at h3
                have a := pString_lt (skipWs rest) k s1 hk
                have b := skipWs_le rest
                have c := skipWs_le s1; rw [hc] at c; simp at c
                have d := skipWs_le s3; rw [hcm] at d; simp at d
                have e := skipWs_le s4
                omega⟩
          | '}' :: s4 => .ok ⟨(.obj ((k, v) :: acc).reverse, s4), by
              show s4.length < rest.length
              simp at h3
              have a := pString_lt (skipWs rest) k s1 hk
              have b := skipWs_le rest
              have c := skipWs_le s1; rw [hc] at c; simp at c
              have d := skipWs_le s3; rw [hcm] at d; simp at d
              omega⟩
          | _ => .error "expected ',' or '}'"
      | _ => .error "expected ':'"
termination_by (s.length, 1)
decreasing_by
  all_goals
    first
      | (have a := pString_lt (skipWs rest) k s1 hk
         have b := skipWs_le rest
         have c := skipWs_le s1; rw [hc] at c; simp at c
         have d := skipWs_le s3; rw [hcm] at d; simp at d
         have e := skipWs_le s4
         simp at h3
         omega)
      | (have a := pString_lt (skipWs rest) k s1 hk
         have b := skipWs_le rest
         have c := skipWs_le s1; rw [hc] at c; simp at c
         omega)

/-- The elements of an array, after the opening bracket. -/
private def pArray (acc : List Doc) (s : Input) : Except String (Parsed s) :=
  match s with
  | ']' :: r => .ok ⟨(.arr acc.reverse, r), by simp⟩
  | rest =>
    match pValue rest with
    | .error e => .error e
    | .ok ⟨(v, s1), h1⟩ =>
      match hc : skipWs s1 with
      | ',' :: s2 =>
        match pArray (v :: acc) (skipWs s2) with
        | .error e => .error e
        | .ok ⟨p, hp⟩ => .ok ⟨p, by
            simp at h1
            have c := skipWs_le s1; rw [hc] at c; simp at c
            have d := skipWs_le s2
            omega⟩
      | ']' :: s2 => .ok ⟨(.arr (v :: acc).reverse, s2), by
          show s2.length < rest.length
          simp at h1
          have c := skipWs_le s1; rw [hc] at c; simp at c
          omega⟩
      | _ => .error "expected ',' or ']'"
termination_by (s.length, 1)
decreasing_by
  all_goals
    first
      | omega
      | (have c := skipWs_le s1; rw [hc] at c; simp at c
         have d := skipWs_le s2
         simp at h1
         omega)

end

def parse (text : String) : Except String Doc :=
  match pValue text.toList with
  | .error e => .error e
  | .ok ⟨(v, rest), _⟩ =>
      match skipWs rest with
      | [] => .ok v
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
