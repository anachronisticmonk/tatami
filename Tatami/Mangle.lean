namespace Tatami

/-- Mangling a JSON member name into an OCaml identifier.

    The design note's example uses names that are already legal, so it does
    not raise the question. Real member names need not be.

    A byte in `a-z`, `A-Z`, `0-9` or `'` passes through; every other byte,
    including `_`, becomes `_` followed by two lowercase hex digits. Escaping
    `_` is what makes `_` an unambiguous escape introducer. The result is
    prefixed with `f_` if it does not begin with a lowercase letter, and
    suffixed with `_` if it is an OCaml keyword.

    Distinct members must map to distinct identifiers, or two columns merge
    silently. That this scheme is injective is not proved here. -/

def keywords : List String :=
  ["and", "as", "assert", "asr", "begin", "class", "constraint", "do", "done",
   "downto", "else", "end", "exception", "external", "false", "for", "fun",
   "function", "functor", "if", "in", "include", "inherit", "initializer",
   "land", "lazy", "let", "lor", "lsl", "lsr", "lxor", "match", "method",
   "mod", "module", "mutable", "new", "nonrec", "object", "of", "open", "or",
   "private", "rec", "sig", "struct", "then", "to", "true", "try", "type",
   "val", "virtual", "when", "while", "with"]

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

private def escapeByte (b : UInt8) : String :=
  let n := b.toNat
  String.ofList ['_', hexDigit (n / 16), hexDigit (n % 16)]

private def passesThrough (b : UInt8) : Bool :=
  let n := b.toNat
  (97 ≤ n && n ≤ 122)      -- a-z
  || (65 ≤ n && n ≤ 90)    -- A-Z
  || (48 ≤ n && n ≤ 57)    -- 0-9
  || n == 39               -- '

private def startsLower (s : String) : Bool :=
  match s.toList with
  | c :: _ => 'a' ≤ c && c ≤ 'z'
  | [] => false

def mangle (s : String) : String :=
  let core :=
    s.toUTF8.foldl (init := "") fun acc b =>
      acc ++ (if passesThrough b then String.ofList [Char.ofNat b.toNat] else escapeByte b)
  let prefixed := if startsLower core then core else "f_" ++ core
  if keywords.contains prefixed then prefixed ++ "_" else prefixed

end Tatami
