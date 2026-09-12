import Tatami.Config
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

/-- A number is an integer only if it was written without a decimal point
    and fits OCaml's native `int`; otherwise it is a float. The design note
    does not discuss numbers, so this rule is ours. -/
def seeScalar (path : String) (j : Doc) : Except Error Seen :=
  match j with
  | .null => .ok .null
  | .bool _ => .ok (.value .bool false)
  | .str _ => .ok (.value .str false)
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
    carry, so it is kept here instead. -/
structure Obs where
  ty : Ty := .bot
  values : Nat := 0
  nulls : Nat := 0
  absent : Nat := 0
  sawInt : Bool := false
  sawFloat : Bool := false
  big : Bool := false
  deriving Repr, Inhabited

def Obs.nullable (o : Obs) : Bool := o.nulls > 0 || o.absent > 0
def Obs.field (o : Obs) : Field := { ty := o.ty, nullable := o.nullable }
/-- Both an integer and a float were seen here, so the column widened. -/
def Obs.widened (o : Obs) : Bool := o.sawInt && o.sawFloat

/-- What has been observed at one table: how many times an object appeared at
    that path, and what each of its members held. The visit count is the
    denominator for absence, and differs per table -- the root table is
    visited once per document, a nested table once per parent that had it. -/
structure TableObs where
  visits : Nat := 0
  /-- of those visits, how many were as a member of a collection -- an array
      element or a map entry. A folded recursive table is reached both ways,
      which is what makes its back-reference optional. -/
  collVisits : Nat := 0
  /-- the table those rows point back to -/
  parent : Option Path := none
  /-- rows are keyed by a string rather than positioned by an index -/
  keyed : Bool := false
  members : List (String × Obs) := []
  /-- whether a collection's members were objects or scalars. One that is some
      of each has no single table shape. -/
  elemObject : Bool := false
  elemScalar : Bool := false
  deriving Inhabited

abbrev Tables := List (Path × TableObs)

def Tables.upsert (ts : Tables) (p : Path) (f : TableObs → TableObs) : Tables :=
  if (ts.lookup p).isSome then
    ts.map fun (q, t) => if q == p then (q, f t) else (q, t)
  else
    ts ++ [(p, f {})]

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

def recordMember (ts : Tables) (p : Path) (k : String) (s : Seen)
    : Except Error Tables := do
  let tbl := (ts.lookup p).getD {}
  let cur := (tbl.members.lookup k).getD {}
  let next : Obs ←
    match s with
    | .null => pure { cur with nulls := cur.nulls + 1 }
    | .value t big =>
        match cur.ty.join t with
        | none =>
            throw (.typeConflict (Path.toString (Path.member p k)) cur.ty.toString t.toString)
        | some j =>
            pure { cur with
              ty := j
              values := cur.values + 1
              big := cur.big || big
              sawInt := cur.sawInt || (t == .int)
              sawFloat := cur.sawFloat || (t == .float) }
  return ts.upsert p fun t =>
    { t with members := t.members.filter (fun q => q.1 != k) ++ [(k, next)] }

/-- The table a collection's rows point back to.

    A row carries a single `parent_id`, so rows reached from two different
    tables cannot be expressed and are refused. This is also what keeps the
    schema a function of the corpus rather than of document order: `parent` is
    the one field that overwrites rather than merges, so without the check the
    answer depends on which document arrived last. -/
def setParent (p : Path) (pp : Path) (t : TableObs) : Except Error (Option Path) :=
  match t.parent with
  | none => .ok (some pp)
  | some q =>
      if q == pp then .ok (some q)
      else .error (.ambiguousParent (Path.toString p) (Path.toString q) (Path.toString pp))

mutual

/-- Walk one object, recording its members and descending into whatever they
    hold.

    `target` is the table this object belongs to, which is not always the path
    it sits at: a path marked recursive folds into an ancestor, and both are
    then the same table. `from?` is set when the object is a member of a
    collection, carrying the table its row points back to and whether it is
    keyed by a string.

    Total, on the measure `Doc.size`. The recursion is on a member of the
    object rather than on the object, so it is not structural, and the four
    functions here replace what were nested `for` loops -- a loop body gives
    the termination checker nothing to attach to. `members` is inlined as the
    match on `j`, because `let ms <- members j` would hide `j = .obj ms` and
    with it the fact that the members are smaller. -/
def observeObject (cfg : Config) (ts : Tables) (target : Path)
    (from? : Option (Path × Bool)) (j : Doc) : Except Error Tables :=
  match j with
  | .obj ms => do
      checkDistinct target ms
      let parent' ← match from? with
        | some (pp, _) => setParent target pp ((ts.lookup target).getD {})
        | none => .ok ((ts.lookup target).getD {}).parent
      let ts := ts.upsert target fun t =>
        { t with
          visits := t.visits + 1
          collVisits := t.collVisits + (if from?.isSome then 1 else 0)
          parent := parent'
          keyed := match from? with | some (_, k) => t.keyed || k | none => t.keyed
          elemObject := t.elemObject || from?.isSome }
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
              let entryTable := cfg.resolve raw
              (do
                let ts ← recordMember ts target k (.value (.coll entryTable) false)
                let ts := ts.upsert entryTable id
                checkDistinct here entries
                have : Doc.sizeVals entries < Doc.sizeVals ((k, Doc.obj entries) :: tl) :=
                  Doc.sizeVals_lt_obj k entries tl
                observeEntries cfg ts target entryTable (Path.toString raw) entries)
            else
              (do
                let child := cfg.resolve here
                let ts ← recordMember ts target k (.value (.ref child) false)
                -- `Doc.obj entries` rather than `v`: the match refines the list
                -- element but not the occurrence of `v`, and the two forms have
                -- to agree for the decrease to be stated
                have : Doc.size (Doc.obj entries)
                     < 1 + Doc.sizeVals ((k, Doc.obj entries) :: tl) :=
                  Doc.size_lt_cons k (Doc.obj entries) tl
                observeObject cfg ts child none (Doc.obj entries))
        | .arr els =>
            (do
              let raw := Path.elem here
              let elemTable := cfg.resolve raw
              let ts ← recordMember ts target k (.value (.coll elemTable) false)
              let ts := ts.upsert elemTable id
              have : Doc.sizeList els < Doc.sizeVals ((k, Doc.arr els) :: tl) :=
                Doc.sizeList_lt_arr k els tl
              observeElems cfg ts target elemTable (Path.toString raw) els)
        | _ =>
            (do
              let s ← seeScalar (Path.toString here) v
              recordMember ts target k s)
      have : Doc.sizeVals tl < Doc.sizeVals ((k, v) :: tl) := Doc.sizeVals_lt (k, v) tl
      observeMembers cfg ts target tl
termination_by (1 + Doc.sizeVals ms, 0)

/-- The elements of one array. An element that is itself an array is refused;
    a scalar element becomes a row with a single `value` column. -/
def observeElems (cfg : Config) (ts : Tables) (target : Path) (elemTable : Path)
    (raw : String) (els : List Doc) : Except Error Tables :=
  match els with
  | [] => .ok ts
  | e :: tl => do
      let ts ←
        match e with
        | .obj ms =>
            have : Doc.size (Doc.obj ms) < 1 + Doc.sizeList (Doc.obj ms :: tl) :=
              Doc.size_lt_consList (Doc.obj ms) tl
            observeObject cfg ts elemTable (some (target, false)) (Doc.obj ms)
        | .arr _ => .error (.nestedArray raw)
        | _ =>
            (do
              let parent' ← setParent elemTable target ((ts.lookup elemTable).getD {})
              let ts := ts.upsert elemTable fun t =>
                { t with visits := t.visits + 1, collVisits := t.collVisits + 1
                       , parent := parent', elemScalar := true }
              let s ← seeScalar raw e
              recordMember ts elemTable "value" s)
      have : Doc.sizeList tl < Doc.sizeList (e :: tl) := Doc.sizeList_lt e tl
      observeElems cfg ts target elemTable raw tl
termination_by (1 + Doc.sizeList els, 0)

/-- The entries of an object marked as a map. Each entry becomes a row keyed
    by its name, so the key itself carries no type. -/
def observeEntries (cfg : Config) (ts : Tables) (target : Path) (entryTable : Path)
    (raw : String) (entries : List (String × Doc)) : Except Error Tables :=
  match entries with
  | [] => .ok ts
  | (k, ev) :: tl => do
      let ts ←
        match ev with
        | .obj ms =>
            have : Doc.size (Doc.obj ms) < 1 + Doc.sizeVals ((k, Doc.obj ms) :: tl) :=
              Doc.size_lt_cons k (Doc.obj ms) tl
            observeObject cfg ts entryTable (some (target, true)) (Doc.obj ms)
        | .arr _ => .error (.mapEntryNotSupported raw "an array")
        | _ =>
            (do
              let parent' ← setParent entryTable target ((ts.lookup entryTable).getD {})
              let ts := ts.upsert entryTable fun t =>
                { t with visits := t.visits + 1, collVisits := t.collVisits + 1
                       , parent := parent', keyed := true, elemScalar := true }
              let s ← seeScalar raw ev
              recordMember ts entryTable "value" s)
      have : Doc.sizeVals tl < Doc.sizeVals ((k, ev) :: tl) := Doc.sizeVals_lt (k, ev) tl
      observeEntries cfg ts target entryTable raw tl
termination_by (1 + Doc.sizeVals entries, 0)

end

/-- Fold every document into one picture of every table.

    Absence is counted once at the end, against each table's own visit count,
    rather than per document as we go: a member first seen late would
    otherwise never record the visits that lacked it. -/
def inferCorpus (cfg : Config) (docs : List Doc) : Except Error Tables := do
  let mut ts : Tables := []
  for d in docs do
    ts ← observeObject cfg ts (cfg.resolve []) none d
  for (p, t) in ts do
    if t.elemObject && t.elemScalar then throw (.mixedElements (Path.toString p))
  -- a marking that matched nothing is a typo, not a no-op
  for m in cfg.maps do
    if (ts.lookup (cfg.resolve (Path.entry m))).isNone then
      throw (.markingMatchedNothing (Path.toString m))
  return ts.map fun (p, t) =>
    (p, { t with members := t.members.map fun (k, o) =>
            (k, { o with absent := t.visits - o.values - o.nulls }) })

/-- Tables in the order OCaml needs them: a module must be declared before it
    is referred to, and a child's path is always longer than its parent's, so
    deepest first puts every child ahead of its parent. Ties are broken
    lexicographically to keep the output stable. -/
def toSchema (ts : Tables) : Schema :=
  let ordered := ts.toArray.qsort fun a b =>
    if a.1.length == b.1.length then
      Path.toString a.1 < Path.toString b.1
    else
      a.1.length > b.1.length
  ordered.toList.map fun (p, t) =>
    { path := p
    , parent := if t.collVisits == 0 then none else t.parent
    , parentOptional := t.collVisits > 0 && t.collVisits < t.visits
    , keyed := t.keyed
    , columns := (t.members.toArray.qsort (fun a b => a.1 < b.1)).toList.map
        fun (k, o) => { name := k, field := o.field } }

end Tatami
