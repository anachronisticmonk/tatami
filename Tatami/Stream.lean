import Tatami.Doc
import Tatami.Error

namespace Tatami
namespace Stream

/-! # Reading a corpus without holding it

    `Doc.parse` takes the whole text and returns one `Doc`. For a corpus that
    is a top-level array, that means the entire file becomes a `List Char` and
    the entire tree is held until inference finishes -- about forty-five times
    the input in memory, which a 1.5 GB corpus cannot survive.

    Nothing here changes the parser. `pValue` stays pure and total; this is a
    loop around it that decides what to hand it. It finds one document's
    boundary in a byte buffer, decodes exactly that, parses it, folds it in,
    and drops it. Memory is then a chunk plus one document plus whatever the
    fold accumulates.

    The boundary scan works on bytes rather than characters, which is what
    makes a chunked read safe: in UTF-8 no multi-byte sequence contains a byte
    below 0x80, so a brace or a quote can be located without decoding, and the
    only text ever decoded is a complete document. A chunk boundary therefore
    cannot split a character in half.

    The loops are bounded rather than `partial`. Each step either consumes a
    byte of the file or reads one, so twice the file size is a bound on both,
    and the bound is real rather than a fuel parameter invented to placate the
    termination checker. -/

private def lbrace : UInt8 := 123   -- '{'
private def rbrace : UInt8 := 125   -- '}'
private def lbrack : UInt8 := 91    -- '['
private def rbrack : UInt8 := 93    -- ']'
private def quote  : UInt8 := 34    -- '"'
private def bslash : UInt8 := 92    -- '\'
private def comma  : UInt8 := 44    -- ','

private def isWsByte (b : UInt8) : Bool :=
  b == 32 || b == 10 || b == 9 || b == 13

/-- The first index at or after `i` holding something other than whitespace. -/
private def skipWsGo (bs : ByteArray) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i => if i < bs.size && isWsByte bs[i]! then skipWsGo bs fuel (i + 1) else i

def skipWs (bs : ByteArray) (i : Nat) : Nat := skipWsGo bs bs.size i

private def spanGo (bs : ByteArray) : Nat → Nat → Bool → Bool → Nat → Option Nat
  | 0, _, _, _, _ => none
  | fuel + 1, depth, inStr, esc, i =>
      if i ≥ bs.size then none
      else
        let c := bs[i]!
        if inStr then
          if esc then spanGo bs fuel depth true false (i + 1)
          else if c == bslash then spanGo bs fuel depth true true (i + 1)
          else if c == quote then spanGo bs fuel depth false false (i + 1)
          else spanGo bs fuel depth true false (i + 1)
        else if c == quote then spanGo bs fuel depth true false (i + 1)
        else if c == lbrace || c == lbrack then spanGo bs fuel (depth + 1) false false (i + 1)
        else if c == rbrace || c == rbrack then
          if depth ≤ 1 then some (i + 1) else spanGo bs fuel (depth - 1) false false (i + 1)
        else spanGo bs fuel depth false false (i + 1)

/-- One past the end of the bracketed value starting at `i`, or `none` when the
    buffer does not hold all of it yet. Finds a boundary; does not parse. -/
def spanValue (bs : ByteArray) (i : Nat) : Option Nat :=
  spanGo bs bs.size 0 false false i

/-- The bytes of one document, decoded and parsed.

    `String.fromUTF8?` cannot fail here -- the slice is a whole document, so it
    is whole characters -- but the failure is reported rather than assumed. -/
def parseSlice (bs : ByteArray) (lo hi : Nat) : Except String Doc :=
  match String.fromUTF8? (bs.extract lo hi) with
  | none => .error "the document is not valid UTF-8"
  | some text => Doc.parse text

/-- What a byte starting a value says the value is, which is all the reader
    needs in order to refuse it with the same words the whole-file path uses. -/
private def describeByte (b : UInt8) : String :=
  if b == quote then "a string"
  else if b == lbrack then "an array"
  else if b == 116 || b == 102 then "a boolean"          -- 't', 'f'
  else if b == 110 then "null"                           -- 'n'
  else if b == 45 || (48 ≤ b && b ≤ 57) then "a number"  -- '-', '0'-'9'
  else "not a JSON value"

/-- What the loop is looking at, having skipped whitespace. -/
private inductive Step where
  | document (start stop : Nat)   -- a complete value spans these
  | done (after : Nat)      -- the array's closing bracket
  | separator (after : Nat) -- a comma
  | needMore                -- the buffer does not reach far enough
  | unexpected (byte : UInt8)

private def look (bs : ByteArray) (i : Nat) : Step :=
  let j := skipWs bs i
  if j ≥ bs.size then .needMore
  else
    let c := bs[j]!
    if c == rbrack then .done (j + 1)
    else if c == comma then .separator (j + 1)
    else if c == lbrace then
      match spanValue bs j with
      | none => .needMore
      | some stop => .document j stop
    else .unexpected c

/-- Fold `step` over the elements of a top-level array, one at a time.

    `size` is the file's size in bytes, which bounds the loop: every iteration
    either consumes a byte already read or reads one, and there are at most
    `size` of each. -/
private def foldArray (h : IO.FS.Handle) (size chunk : Nat) (start : Nat) (bs : ByteArray)
    (init : σ) (step : σ → Doc → IO (Except String σ)) : IO (Except String σ) := do
  let rec go : Nat → ByteArray → Nat → σ → Nat → Bool → IO (Except String σ)
    | 0, _, _, st, _, _ => return .ok st
    | fuel + 1, bs, i, st, idx, eof => do
        -- reclaim what has been consumed before it grows without bound
        let (bs, i) := if i > 0 && i * 2 > bs.size then (bs.extract i bs.size, 0) else (bs, i)
        match look bs i with
        | .done _ => return .ok st
        | .separator after => go fuel bs after st idx eof
        | .unexpected c =>
            return .error (Error.arrayElementNotObject idx (describeByte c)).toString
        | .document start stop =>
            match parseSlice bs start stop with
            | .error e => return .error e
            | .ok d =>
                match ← step st d with
                | .error e => return .error e
                | .ok st => go fuel bs stop st (idx + 1) eof
        | .needMore =>
            if eof then return .error "the top-level array is not closed"
            else
              let more ← h.read chunk.toUSize
              if more.size == 0 then go fuel bs i st idx true
              else go fuel (bs ++ more) i st idx eof
  go (2 * size + 2) bs start init 0 false

/-- Read the whole of what is left, for the one shape that cannot be streamed. -/
private def readRest (h : IO.FS.Handle) (size chunk : Nat) (bs : ByteArray) : IO ByteArray := do
  let rec go : Nat → ByteArray → IO ByteArray
    | 0, acc => return acc
    | fuel + 1, acc => do
        let more ← h.read chunk.toUSize
        if more.size == 0 then return acc else go fuel (acc ++ more)
  go (size + 1) bs

/-- Hand every document in the file to `step`, one at a time.

    A top-level array is streamed: only one element is ever decoded, parsed and
    held. A lone top-level object is not -- there is nothing to stream, so it is
    read whole, which is what the playground and the small cases do anyway.

    `size` is the file's size in bytes. Every iteration either consumes a byte
    already read or reads one, and there are at most `size` of each, so twice
    that bounds the loop. -/
def foldDocuments (h : IO.FS.Handle) (size chunk : Nat) (init : σ)
    (step : σ → Doc → IO (Except String σ)) : IO (Except String σ) := do
  let first ← h.read chunk.toUSize
  let start := skipWs first 0
  if start ≥ first.size then return .error "the input is empty"
  else if first[start]! == lbrack then
    foldArray h size chunk (start + 1) first init step
  else if first[start]! == lbrace then
    let whole ← readRest h size chunk first
    match parseSlice whole start whole.size with
    | .error e => return .error e
    | .ok d => step init d
  else
    return .error "the top-level value is not an object or an array of objects"

end Stream
end Tatami
