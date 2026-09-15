import Tatami.Doc
import Tatami.Sql

namespace Tatami

/-! # Shredding a document into rows

    The second walk. `Tatami.Infer` walks a document to learn the schema; this
    walks it again to produce the rows, in the column order `layoutOf` fixed,
    so the two cannot disagree about what a table holds.

    Output is Postgres COPY text rather than `INSERT` statements. Measured on
    fifty thousand rows into one table: an `INSERT` each takes 35 s, a single
    `COPY` takes 0.18 s, and the corpus is about twenty-one million rows.

    Keys are minted where a document has no `id` of its own. The generator is
    the only thing that sees the whole corpus, so it is the only thing that can
    hand them out; determinism across runs was not asked for, so they come from
    a small PRNG seeded once.

    Like the walk it mirrors, this recurses on the member *list* rather than on
    a member looked up by name: the size lemmas relate a list to its tail, and
    there is no lemma about a lookup. The cells are therefore collected by
    walking the members once and assembled into column order afterwards. -/

/-- xorshift64*. Small, pure, and adequate: keys have to be distinct within a
    run, not unguessable. -/
structure Rng where
  state : UInt64
  deriving Inhabited

def Rng.next (g : Rng) : UInt64 × Rng :=
  let x := g.state
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 2685821657736338717, { state := x })

private def nibble (v : UInt64) : Char :=
  let n := (v &&& 15).toNat
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

private def hexGo : Nat → UInt64 → List Char → List Char
  | 0, _, acc => acc
  | n + 1, v, acc => hexGo n (v >>> 4) (nibble v :: acc)

private def hex (n : Nat) (v : UInt64) : String := String.ofList (hexGo n v [])

/-- A version 4 uuid in canonical form. -/
def Rng.uuid (g : Rng) : String × Rng :=
  let (a, g) := g.next
  let (b, g) := g.next
  let s := hex 8 (a >>> 32) ++ "-" ++ hex 4 (a >>> 16) ++ "-4" ++ hex 3 a ++ "-"
        ++ hex 1 ((8 : UInt64) ||| ((b >>> 60) &&& 3)) ++ hex 3 (b >>> 48) ++ "-"
        ++ hex 12 b
  (s, g)

/-- One cell of COPY text. `none` is SQL NULL, which the writer spells `\N`. -/
abbrev Cell := Option String

structure Row where
  table : Path
  cells : List Cell
  deriving Repr

/-- A value as the text COPY expects.

    A number keeps the literal it was written with: our reader never normalised
    it, so this round-trips exactly, which `%.17g` would not. A column that was
    never given a value is null whatever arrives at it. -/
def cellOf (ty : Ty) (v : Doc) : Cell :=
  if ty == .bot then none
  else match v with
    | .null => none
    | .bool b => some (if b then "t" else "f")
    | .num lit => some lit
    | .str s => some s
    | .obj _ => none
    | .arr _ => none

/-- Escaped for COPY text: tab separates, backslash escapes, `\N` is NULL. -/
def escapeCell : Cell → String
  | none => "\\N"
  | some v =>
      String.ofList (v.toList.flatMap fun c =>
        if c == '\\' then ['\\', '\\']
        else if c == '\t' then ['\\', 't']
        else if c == '\n' then ['\\', 'n']
        else if c == '\r' then ['\\', 'r']
        else [c])

def Row.print (r : Row) : String :=
  String.intercalate "\t" (r.cells.map escapeCell) ++ "\n"

/-- What the walk carries: where each table's columns are, the key source, and
    the rows produced, newest first. -/
structure Shred where
  layouts : List (Path × List Col)
  rng : Rng
  rows : List Row := []

def Shred.layoutFor (st : Shred) (p : Path) : List Col :=
  (st.layouts.lookup p).getD []

private def Shred.mint (st : Shred) : Cell × Shred :=
  let (u, g) := st.rng.uuid
  (some u, { st with rng := g })

/-- A collection of scalars: the element is the single `value` column. -/
def scalarRow (st : Shred) (table : Path) (parentKey pos : Cell) (v : Doc) : Shred :=
  let (key, st) := st.mint
  let cells := (st.layoutFor table).map fun c =>
    match c.kind with
    | .key => key
    | .parent => parentKey
    | .position => pos
    | .member _ => cellOf c.ty v
  { st with rows := { table := table, cells := cells } :: st.rows }

mutual

/-- One object into one row of `target`, and every row beneath it.

    Its key is settled first, because the collections beneath it point back at
    it; its `ref` members are shredded on the way past, because each supplies
    the key that goes in this row. -/
def shredObject (st : Shred) (target : Path) (parentKey pos : Doc → Cell)
    (j : Doc) : Except Error (Cell × Shred) :=
  match j with
  | .obj ms => do
      let cols := st.layoutFor target
      let (key, st) : Cell × Shred :=
        match cols.find? (·.kind == .key) with
        | none => (none, st)
        | some c =>
            match ms.lookup "id" with
            | some v => (cellOf c.ty v, st)
            | none => st.mint
      let (vals, st) ← shredMembers st target cols key [] ms
      let cells := cols.map fun c =>
        match c.kind with
        | .key => key
        | .parent => parentKey j
        | .position => pos j
        | .member src => (vals.lookup src).getD none
      return (key, { st with rows := { table := target, cells := cells } :: st.rows })
  | other => .error (.notObjectOrArray (Doc.describe other))
termination_by (j.size, 1)

/-- The members, in the order they were written. A member with a column is a
    cell; one without is a collection, whose rows point back at `key`. -/
def shredMembers (st : Shred) (target : Path) (cols : List Col) (key : Cell)
    (acc : List (String × Cell)) (ms : List (String × Doc)) :
    Except Error (List (String × Cell) × Shred) :=
  match ms with
  | [] => .ok (acc, st)
  | (k, v) :: tl => do
      let here := Path.member target k
      let col := cols.find? (·.kind == .member k)
      let (acc, st) ←
        match v with
        | .obj entries =>
            match col.map (·.ty) with
            | some (Ty.ref child) =>
                (do
                  have : Doc.size (Doc.obj entries)
                       < 1 + Doc.sizeVals ((k, Doc.obj entries) :: tl) :=
                    Doc.size_lt_cons k (Doc.obj entries) tl
                  let (ck, st) ← shredObject st child (fun _ => none) (fun _ => none)
                                   (Doc.obj entries)
                  return (acc ++ [(k, ck)], st))
            | _ =>
                -- no column, so the members are rows of their own table
                (do
                  have : Doc.sizeVals entries < Doc.sizeVals ((k, Doc.obj entries) :: tl) :=
                    Doc.sizeVals_lt_obj k entries tl
                  let st ← shredEntries st (Path.entry here) key entries
                  return (acc, st))
        | .arr els =>
            (do
              have : Doc.sizeList els < Doc.sizeVals ((k, Doc.arr els) :: tl) :=
                Doc.sizeList_lt_arr k els tl
              let st ← shredElems st (Path.elem here) key 0 els
              return (acc, st))
        | scalar =>
            .ok (acc ++ [(k, match col with | some c => cellOf c.ty scalar | none => none)], st)
      have : Doc.sizeVals tl < Doc.sizeVals ((k, v) :: tl) := Doc.sizeVals_lt (k, v) tl
      shredMembers st target cols key acc tl
termination_by (1 + Doc.sizeVals ms, 0)

def shredElems (st : Shred) (elemTable : Path) (parentKey : Cell) (i : Nat)
    (els : List Doc) : Except Error Shred :=
  match els with
  | [] => .ok st
  | e :: tl => do
      let st ←
        match e with
        | .obj ms =>
            (do
              have : Doc.size (Doc.obj ms) < 1 + Doc.sizeList (Doc.obj ms :: tl) :=
                Doc.size_lt_consList (Doc.obj ms) tl
              let (_, st) ← shredObject st elemTable (fun _ => parentKey)
                              (fun _ => some (toString i)) (Doc.obj ms)
              return st)
        | .arr _ => .error (.nestedArray (Path.toString elemTable))
        | scalar => .ok (scalarRow st elemTable parentKey (some (toString i)) scalar)
      have : Doc.sizeList tl < Doc.sizeList (e :: tl) := Doc.sizeList_lt e tl
      shredElems st elemTable parentKey (i + 1) tl
termination_by (1 + Doc.sizeList els, 0)

def shredEntries (st : Shred) (entryTable : Path) (parentKey : Cell)
    (entries : List (String × Doc)) : Except Error Shred :=
  match entries with
  | [] => .ok st
  | (k, ev) :: tl => do
      let st ←
        match ev with
        | .obj ms =>
            (do
              have : Doc.size (Doc.obj ms) < 1 + Doc.sizeVals ((k, Doc.obj ms) :: tl) :=
                Doc.size_lt_cons k (Doc.obj ms) tl
              let (_, st) ← shredObject st entryTable (fun _ => parentKey)
                              (fun _ => some k) (Doc.obj ms)
              return st)
        | .arr _ => .error (.mapEntryNotSupported (Path.toString entryTable) "an array")
        | scalar => .ok (scalarRow st entryTable parentKey (some k) scalar)
      have : Doc.sizeVals tl < Doc.sizeVals ((k, ev) :: tl) := Doc.sizeVals_lt (k, ev) tl
      shredEntries st entryTable parentKey tl
termination_by (1 + Doc.sizeVals entries, 0)

end

/-- One document's rows, in the order they were produced. -/
def shredDocument (layouts : List (Path × List Col)) (rng : Rng) (root : Path)
    (d : Doc) : Except Error (List Row × Rng) := do
  let (_, st) ← shredObject { layouts := layouts, rng := rng } root
                  (fun _ => none) (fun _ => none) d
  return (st.rows.reverse, st.rng)

end Tatami
