import Tatami.Config
import Tatami.Sorted
import Tatami.Doc
import Tatami.Error
import Tatami.Path
import Tatami.Ty
import Tatami.Schema

namespace Tatami

/-- The largest integer OCaml's native `int` holds on a 64-bit platform. -/
def maxNativeInt : Nat := 4611686018427387903

/-- What one value contributes at a member. `null` carries no type of its
    own; it only makes the member nullable. -/
inductive Seen where
  | null
  | value (ty : Ty) (big : Bool)

/-- The canonical uuid form: 8-4-4-4-12 hex digits with hyphens.

    Checked on the text, so a member is typed `uuid` only when every value
    seen there had this shape. One ordinary string and `Ty.join` widens it
    back to `str`, which is what keeps this a type rather than a guess. -/
def isUuid (s : String) : Bool :=
  let cs := s.toList
  if cs.length != 36 then false
  else
    let hex (c : Char) : Bool :=
      ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
    let rec go : Nat → List Char → Bool
      | _, [] => true
      | i, c :: tl =>
          (if i == 8 || i == 13 || i == 18 || i == 23 then c == '-' else hex c)
          && go (i + 1) tl
    go 0 cs

/-- A number is an integer only if it was written without a decimal point
    and fits OCaml's native `int`; otherwise it is a float. The design note
    does not discuss numbers, so this rule is ours. -/
def seeScalar (path : String) (j : Doc) : Except Error Seen :=
  match j with
  | .null => .ok .null
  | .bool _ => .ok (.value .bool false)
  | .str v => .ok (.value (if isUuid v then .uuid else .str) false)
  | .num lit =>
      -- written with a decimal point or an exponent, so a float
      if lit.any (fun c => c == '.' || c == 'e' || c == 'E') then
        .ok (.value .float false)
      else
        match lit.toInt? with
        | some n => if n.natAbs > maxNativeInt then .ok (.value .float true)
                    else .ok (.value .int false)
        | none => .ok (.value .float true)
  -- objects and arrays are handled by the caller, which knows the path they
  -- sit at; these cases are unreachable from there
  | .obj _ => .ok (.value .bot false)
  | .arr _ => .error (.nestedArray path)

/-- What has been observed at one member. The counts separate an explicit
    `null` from an absent key -- a distinction the generated `option` cannot
    carry, so it is kept here instead.

    `seen` is the *set* of types the values there had, kept in order, rather
    than their running join. Union of sets is commutative and associative with
    nothing to prove, which is what makes the corpus fold independent of the
    order documents arrive in; the join is taken once, at the end. It also
    lets a conflict name every type involved rather than the two that happened
    to meet first. -/
structure Obs where
  seen : List Ty := []
  values : Nat := 0
  nulls : Nat := 0
  absent : Nat := 0
  big : Bool := false
  deriving Repr, Inhabited

def Obs.nullable (o : Obs) : Bool := o.nulls > 0 || o.absent > 0

/-- The one type admitting everything seen here, if there is one. `none` is
    the case the corpus is refused for. -/
def Obs.joined (o : Obs) : Option Ty :=
  o.seen.foldl (fun acc t => acc.bind (Ty.join · t)) (some .bot)

/-- `joined` is `some` for every member of a schema that was accepted, which
    `inferFinish` checks before anything gets here. -/
def Obs.field (o : Obs) : Field :=
  { ty := o.joined.getD .bot, nullable := o.nullable }

/-- Both an integer and a float were seen here, so the column widened. -/
def Obs.widened (o : Obs) : Bool := o.seen.contains .int && o.seen.contains .float

def Obs.merge (a b : Obs) : Obs :=
  { seen := unionBy Ty.lt (· == ·) a.seen b.seen
    values := a.values + b.values
    nulls := a.nulls + b.nulls
    absent := a.absent + b.absent
    big := a.big || b.big }

/-- What has been observed at one table: how many times an object appeared at
    that path, and what each of its members held. The visit count is the
    denominator for absence, and differs per table -- the root table is
    visited once per document, a nested table once per parent that had it.

    Nothing here records where a row came from. Since a table is identified by
    its path and nothing folds, the table it points back to and whether it is
    keyed are functions of that path; `toSchema` reads them off it. Every field
    that remains accumulates, so the order documents arrive in cannot matter. -/
structure TableObs where
  visits : Nat := 0
  members : List (String × Obs) := []
  /-- whether a collection's members were objects or scalars. One that is some
      of each has no single table shape. -/
  elemObject : Bool := false
  elemScalar : Bool := false
  deriving Inhabited

def TableObs.merge (a b : TableObs) : TableObs :=
  { visits := a.visits + b.visits
    members := mergeBy (· < ·) (· == ·) Obs.merge a.members b.members
    elemObject := a.elemObject || b.elemObject
    elemScalar := a.elemScalar || b.elemScalar }

/-- Kept in path order, so that two corpora differing only in the order their
    documents arrived produce the same list and not merely the same set. -/
abbrev Tables := List (Path × TableObs)

def Tables.merge (a b : Tables) : Tables :=
  mergeBy Path.lt (· == ·) TableObs.merge a b

def Tables.upsert (ts : Tables) (p : Path) (f : TableObs → TableObs) : Tables :=
  if (ts.lookup p).isSome then
    ts.map fun (q, t) => if q == p then (q, f t) else (q, t)
  else
    insertBy Path.lt (· == ·) (fun _ new => new) p (f {}) ts

/-- No longer used by the walk, which matches on `j` itself so that the
    termination argument can see the members are smaller. Kept because it is
    the declarative statement of what an object is, and the specification
    work will want it. -/
def members (j : Doc) : Except Error (List (String × Doc)) :=
  match j with
  | .obj ms => .ok ms
  | other => .error (.notObjectOrArray (Doc.describe other))

/-- A repeated member. Our reader keeps both bindings, so this is the point
    at which the document is refused. -/
def checkDistinct (p : Path) (ms : List (String × Doc)) : Except Error Unit :=
  let rec go (seen : List String) : List (String × Doc) → Except Error Unit
    | [] => .ok ()
    | (k, _) :: tl =>
        if seen.contains k then .error (.duplicateMember (Path.toString p) k)
        else go (k :: seen) tl
  go [] ms

/-- A lone object is a corpus of one; a top-level array is a corpus of its
    elements, each of which must be an object. -/
def documents (j : Doc) : Except Error (List Doc) :=
  match j with
  | .obj _ => .ok [j]
  | .arr elements =>
      let rec go (i : Nat) (acc : List Doc) : List Doc → Except Error (List Doc)
        | [] => .ok acc.reverse
        | (d@(.obj _)) :: tl => go (i + 1) (d :: acc) tl
        | other :: _ => .error (.arrayElementNotObject i (Doc.describe other))
      go 0 [] elements
  | other => .error (.notObjectOrArray (Doc.describe other))

/-- One observation at one member. Nothing is refused here any more: a type
    conflict is a property of the set of types seen, and that set is only
    complete once the whole corpus has been read. -/
def recordMember (ts : Tables) (p : Path) (k : String) (s : Seen) : Tables :=
  let one : Obs :=
    match s with
    | .null => { nulls := 1 }
    | .value t big => { seen := [t], values := 1, big := big }
  ts.upsert p fun t =>
    { t with members := insertBy (· < ·) (· == ·) Obs.merge k one t.members }

mutual

/-- Walk one object, recording its members and descending into whatever they
    hold.

    `target` is the table this object belongs to, which is simply the path it
    sits at -- nothing folds, so the two coincide. `inCollection` says whether
    the object arrived as a member of a collection. That is the only thing
    about a row's provenance not already recoverable from the path, and it is
    needed solely to notice a collection holding both objects and scalars.

    Total, on the measure `Doc.size`. The recursion is on a member of the
    object rather than on the object, so it is not structural, and the four
    functions here replace what were nested `for` loops -- a loop body gives
    the termination checker nothing to attach to. `members` is inlined as the
    match on `j`, because `let ms <- members j` would hide `j = .obj ms` and
    with it the fact that the members are smaller. -/
def observeObject (cfg : Config) (ts : Tables) (target : Path)
    (inCollection : Bool) (j : Doc) : Except Error Tables :=
  match j with
  | .obj ms => do
      checkDistinct target ms
      let ts := ts.upsert target fun t =>
        { t with
          visits := t.visits + 1
          elemObject := t.elemObject || inCollection }
      observeMembers cfg ts target ms
  | other => .error (.notObjectOrArray (Doc.describe other))
termination_by (j.size, 1)

/-- The members of one object, in the order they were written. -/
def observeMembers (cfg : Config) (ts : Tables) (target : Path)
    (ms : List (String × Doc)) : Except Error Tables :=
  match ms with
  | [] => .ok ts
  | (k, v) :: tl => do
      let here := Path.member target k
      let ts ←
        match v with
        | .obj entries =>
            if cfg.isMap here then
              -- the members are data: each becomes a row keyed by its name
              let raw := Path.entry here
              (do
                let ts := recordMember ts target k (.value (.coll raw) false)
                let ts := ts.upsert raw id
                checkDistinct here entries
                have : Doc.sizeVals entries < Doc.sizeVals ((k, Doc.obj entries) :: tl) :=
                  Doc.sizeVals_lt_obj k entries tl
                observeEntries cfg ts raw (Path.toString raw) entries)
            else
              (do
                let ts := recordMember ts target k (.value (.ref here) false)
                -- `Doc.obj entries` rather than `v`: the match refines the list
                -- element but not the occurrence of `v`, and the two forms have
                -- to agree for the decrease to be stated
                have : Doc.size (Doc.obj entries)
                     < 1 + Doc.sizeVals ((k, Doc.obj entries) :: tl) :=
                  Doc.size_lt_cons k (Doc.obj entries) tl
                observeObject cfg ts here false (Doc.obj entries))
        | .arr els =>
            (do
              let raw := Path.elem here
              let ts := recordMember ts target k (.value (.coll raw) false)
              let ts := ts.upsert raw id
              have : Doc.sizeList els < Doc.sizeVals ((k, Doc.arr els) :: tl) :=
                Doc.sizeList_lt_arr k els tl
              observeElems cfg ts raw (Path.toString raw) els)
        | _ =>
            (do
              let s ← seeScalar (Path.toString here) v
              .ok (recordMember ts target k s))
      have : Doc.sizeVals tl < Doc.sizeVals ((k, v) :: tl) := Doc.sizeVals_lt (k, v) tl
      observeMembers cfg ts target tl
termination_by (1 + Doc.sizeVals ms, 0)

/-- The elements of one array. An element that is itself an array is refused;
    a scalar element becomes a row with a single `value` column. -/
def observeElems (cfg : Config) (ts : Tables) (elemTable : Path)
    (raw : String) (els : List Doc) : Except Error Tables :=
  match els with
  | [] => .ok ts
  | e :: tl => do
      let ts ←
        match e with
        | .obj ms =>
            have : Doc.size (Doc.obj ms) < 1 + Doc.sizeList (Doc.obj ms :: tl) :=
              Doc.size_lt_consList (Doc.obj ms) tl
            observeObject cfg ts elemTable true (Doc.obj ms)
        | .arr _ => .error (.nestedArray raw)
        | _ =>
            (do
              let ts := ts.upsert elemTable fun t =>
                { t with visits := t.visits + 1, elemScalar := true }
              let s ← seeScalar raw e
              .ok (recordMember ts elemTable "value" s))
      have : Doc.sizeList tl < Doc.sizeList (e :: tl) := Doc.sizeList_lt e tl
      observeElems cfg ts elemTable raw tl
termination_by (1 + Doc.sizeList els, 0)

/-- The entries of an object marked as a map. Each entry becomes a row keyed
    by its name, so the key itself carries no type. -/
def observeEntries (cfg : Config) (ts : Tables) (entryTable : Path)
    (raw : String) (entries : List (String × Doc)) : Except Error Tables :=
  match entries with
  | [] => .ok ts
  | (k, ev) :: tl => do
      let ts ←
        match ev with
        | .obj ms =>
            have : Doc.size (Doc.obj ms) < 1 + Doc.sizeVals ((k, Doc.obj ms) :: tl) :=
              Doc.size_lt_cons k (Doc.obj ms) tl
            observeObject cfg ts entryTable true (Doc.obj ms)
        | .arr _ => .error (.mapEntryNotSupported raw "an array")
        | _ =>
            (do
              let ts := ts.upsert entryTable fun t =>
                { t with visits := t.visits + 1, elemScalar := true }
              let s ← seeScalar raw ev
              .ok (recordMember ts entryTable "value" s))
      have : Doc.sizeVals tl < Doc.sizeVals ((k, ev) :: tl) := Doc.sizeVals_lt (k, ev) tl
      observeEntries cfg ts entryTable raw tl
termination_by (1 + Doc.sizeVals entries, 0)

end

/-- One document on its own, observed from nothing.

    Each document is observed independently and the results are merged, rather
    than threaded through a shared accumulator. The merge is commutative and
    associative because every field of it is -- counts add, type sets union,
    flags disjoin -- so the corpus's schema does not depend on the order the
    documents arrived in. That is `infer_perm`, and this is what makes it hold
    by construction rather than by proof about the walk. -/
def observeDocument (cfg : Config) (d : Doc) : Except Error Tables :=
  observeObject cfg [] [] false d

/-- One document folded in. The accumulator is bounded by the *schema*, not by
    the corpus, which is what lets a reader hand documents over one at a time
    and drop each one after. -/
def inferStep (cfg : Config) (ts : Tables) (d : Doc) : Except Error Tables := do
  return ts.merge (← observeDocument cfg d)

/-- What can only be settled once every document has been seen: a collection
    holding both objects and scalars, a marking that matched nothing, and the
    absent counts, which are against each table's own visit total. -/
def inferFinish (cfg : Config) (ts : Tables) : Except Error Tables := do
  -- a member holding values with no common type. Checked here rather than
  -- during the walk because the set of types seen is only complete once the
  -- whole corpus has been read, which is what lets the walk merge in any order
  for (p, t) in ts do
    for (k, o) in t.members do
      if o.joined.isNone then
        throw (.typeConflict (Path.toString (Path.member p k))
                 (String.intercalate ", " (o.seen.map Ty.toString)))
  for (p, t) in ts do
    if t.elemObject && t.elemScalar then throw (.mixedElements (Path.toString p))
  -- a marking that matched nothing is a typo, not a no-op
  for m in cfg.maps do
    if (ts.lookup (Path.entry m)).isNone then
      throw (.markingMatchedNothing (Path.toString m))
  return ts.map fun (p, t) =>
    (p, { t with members := t.members.map fun (k, o) =>
            (k, { o with absent := t.visits - o.values - o.nulls }) })

/-- Fold every document into one picture of every table. The list form; a
    reader that cannot hold the corpus uses `inferStep` and `inferFinish`
    directly.

    Absence is counted at the end, against each table's own visit count,
    rather than per document as we go: a member first seen late would
    otherwise never record the visits that lacked it. -/
def inferCorpus (cfg : Config) (docs : List Doc) : Except Error Tables := do
  let tss ← docs.mapM (observeDocument cfg)
  inferFinish cfg (tss.foldl Tables.merge [])

/-- Tables in the order OCaml needs them: a module must be declared before it
    is referred to, and a child's path is always longer than its parent's, so
    deepest first puts every child ahead of its parent. Ties are broken
    lexicographically to keep the output stable. -/
def toSchema (ts : Tables) : Schema :=
  let ordered := sortBy (fun a b =>
    if a.1.length == b.1.length then
      Path.toString a.1 < Path.toString b.1
    else
      a.1.length > b.1.length) ts
  ordered.map fun (p, t) =>
    { path := p
    , parent := Path.parentOfElement p
    , keyed := Path.isEntry p
    -- no sort: `TableObs.merge` and `recordMember` both keep the members in
    -- name order, so they arrive sorted. `Proofs.Merge` states that as
    -- `TableObsOk` and `Proofs.Walk` proves the walk maintains it.
    , columns := t.members.map fun (k, o) => { name := k, field := o.field } }

end Tatami
