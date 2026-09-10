namespace Tatami

/-- Mangling a JSON member name into an OCaml identifier.

    The design note's example uses names that are already legal, so it does
    not raise the question. Real member names need not be.

    A byte in `a-z`, `A-Z`, `0-9` or `'` passes through; every other byte,
    including `_`, becomes `_` followed by two lowercase hex digits. Escaping
    `_` is what makes `_` an unambiguous escape introducer. The result is
    prefixed with `f__` if it does not begin with a lowercase letter, and
    suffixed with `_` if it is an OCaml keyword.

    The prefix is `f__`, not `f_`, because `f_` is reachable: `_` escapes to
    `_5f`, so the member `f_61` has core `f_5f61`, which begins with a
    lowercase letter and is left unprefixed. The member `5f61` does need the
    prefix, and with `f_` it would land on `f_5f61` as well. No core contains
    `__` at all -- the two characters after an escape's `_` are hex digits --
    so `f__` is unreachable and the prefixed and unprefixed halves stay
    disjoint.

    Distinct members must map to distinct identifiers, or two columns merge
    silently. That is `mangle_injective` in `Proofs.Mangle`.

    Everything below works on `List Char` and only becomes a `String` at the
    end. That is for the proof's benefit: the encoding used to be a fold over
    `s.toUTF8`, and `ByteArray.foldl` is an index loop with no bridge to a
    list fold in core, so there was nothing to induct along. -/

def keywords : List String :=
  ["and", "as", "assert", "asr", "begin", "class", "constraint", "do", "done",
   "downto", "else", "end", "exception", "external", "false", "for", "fun",
   "function", "functor", "if", "in", "include", "inherit", "initializer",
   "land", "lazy", "let", "lor", "lsl", "lsr", "lxor", "match", "method",
   "mod", "module", "mutable", "new", "nonrec", "object", "of", "open", "or",
   "private", "rec", "sig", "struct", "then", "to", "true", "try", "type",
   "val", "virtual", "when", "while", "with"]

/-- `n < 16` as a lowercase hex digit. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def passesThrough (b : UInt8) : Bool :=
  let n := b.toNat
  (97 ≤ n && n ≤ 122)      -- a-z
  || (65 ≤ n && n ≤ 90)    -- A-Z
  || (48 ≤ n && n ≤ 57)    -- 0-9
  || n == 39               -- '

/-- One byte: itself when it passes through, otherwise `_` and two hex
    digits. -/
def encodeByte (b : UInt8) : List Char :=
  if passesThrough b then [Char.ofNat b.toNat]
  else ['_', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- Structural recursion rather than a fold, so the proof can induct on it. -/
def encodeBytes : List UInt8 → List Char
  | [] => []
  | b :: bs => encodeByte b ++ encodeBytes bs

def startsLower : List Char → Bool
  | c :: _ => 'a' ≤ c && c ≤ 'z'
  | [] => false

def isKeyword (p : List Char) : Bool := keywords.contains (String.ofList p)

/-- Prefix a core that does not begin with a lowercase letter. -/
def prefixedCore (core : List Char) : List Char :=
  if startsLower core then core else 'f' :: '_' :: '_' :: core

/-- Suffix an identifier that collides with an OCaml keyword. -/
def keywordSuffixed (p : List Char) : List Char :=
  if isKeyword p then p ++ ['_'] else p

/-- The identifier as characters: encode, prefix if it does not begin with a
    lowercase letter, suffix if it is a keyword. The three layers are named
    separately because each is proved injective on its own in
    `Proofs.Mangle`. -/
def mangleChars (s : String) : List Char :=
  -- `.data.toList` rather than `.toList`: `ByteArray.toList` is defined by a
  -- loop, whereas this route has `Array.ext'` and `ByteArray.ext` to hand, and
  -- injectivity of the whole depends on getting back from bytes to the string
  keywordSuffixed (prefixedCore (encodeBytes s.toUTF8.data.toList))

def mangle (s : String) : String := String.ofList (mangleChars s)

end Tatami
