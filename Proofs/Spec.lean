import Tatami.Infer
import Proofs.Lattice

/-!
# What it means for a schema to describe a document

The implementation is the only account of a schema the project has had so far:
`inferCorpus` computes one, and "correct" has meant "whatever that produces".
This file breaks that circle by saying, separately and declaratively, when a
document *is described by* a schema. `Proofs.Inference` then claims the two
agree.

**Written independently on purpose.** If `Conforms` were defined by calling
`observeObject` or `seeScalar`, the theorems about it would say "inference
agrees with inference" -- true, and worth nothing. So `scalarTy` below
duplicates the rule in `seeScalar` rather than reusing it, and the two are
connected by a lemma (`scalarTy_seeScalar`) that can fail if they drift apart.
`Tatami.Infer` is imported for `maxNativeInt` and `isUuid`, which are facts
about OCaml's `int` and about uuid syntax rather than anything about
inference.

Nothing here mentions `Config` at all. The root table sits at the empty path,
and from there conformance follows the schema's own `ref` and `coll` links. That
matters for minimality, which compares two different schemas and has to judge
them by the same yardstick.
-/

namespace Tatami

def Doc.isScalar : Doc → Bool
  | .obj _ => false
  | .arr _ => false
  | _ => true

/-- The type a scalar carries. The same rule as `seeScalar`, said without
    reference to it: a number written with a point or an exponent is a float,
    an integer too large for OCaml's `int` is a float, anything else integral
    is an `int`, and a uuid-shaped string is a `uuid` rather than a `str`.
    `null` carries no type of its own. -/
def scalarTy : Doc → Option Ty
  | .null => none
  | .bool _ => some .bool
  | .str v => some (if isUuid v then .uuid else .str)
  | .num lit =>
      if lit.any (fun c => c == '.' || c == 'e' || c == 'E') then some .float
      else
        match lit.toInt? with
        | some n => if n.natAbs > maxNativeInt then some .float else some .int
        | none => some .float
  | .obj _ => none
  | .arr _ => none

mutual

/-- The object `d`, sitting at the table whose path is `p`, is described by
    schema `s`: every member it has is a column holding a matching value, and
    every column it lacks is optional. -/
inductive ConformsObj (s : Schema) : Path → Doc → Prop where
  | obj {p : Path} {ms : List (String × Doc)} {t : Table} :
      s.find? (fun u => u.path == p) = some t →
      MembersMatch s t ms →
      (∀ c ∈ t.columns, ms.lookup c.name = none → c.field.nullable = true) →
      ConformsObj s p (.obj ms)

/-- Each member in turn. Written as a list recursion rather than
    `∀ k v, (k, v) ∈ ms → ∃ c ∈ t.columns, ...` because an `∃` wrapping a
    mutually inductive occurrence is not a legal nested inductive; the column
    becomes a constructor argument instead. -/
inductive MembersMatch (s : Schema) : Table → List (String × Doc) → Prop where
  | nil {t : Table} : MembersMatch s t []
  | cons {t : Table} {k : String} {v : Doc} {tl : List (String × Doc)} {c : Column} :
      c ∈ t.columns → c.name = k → MatchesField s c.field v →
      MembersMatch s t tl → MembersMatch s t ((k, v) :: tl)

/-- The value `v` is described by field `f`. The `scalar` case is where the
    type order earns its keep: an `int` value matches a `float` column. -/
inductive MatchesField (s : Schema) : Field → Doc → Prop where
  | null {f : Field} : f.nullable = true → MatchesField s f .null
  | scalar {f : Field} {v : Doc} {ty : Ty} :
      scalarTy v = some ty → Ty.le ty f.ty → MatchesField s f v
  | ref {f : Field} {v : Doc} {q : Path} :
      f.ty = .ref q → ConformsObj s q v → MatchesField s f v
  | arr {f : Field} {els : List Doc} {q : Path} :
      f.ty = .coll q → q.isElement = true →
      (∀ e ∈ els, ConformsElem s q e) → MatchesField s f (.arr els)
  | map {f : Field} {ms : List (String × Doc)} {q : Path} :
      f.ty = .coll q → q.isEntry = true →
      (∀ k v, (k, v) ∈ ms → ConformsElem s q v) → MatchesField s f (.obj ms)

/-- One element of an array or one entry of a map: either a row of its own, or
    a scalar sitting in the generated `value` column. -/
inductive ConformsElem (s : Schema) : Path → Doc → Prop where
  | row {q : Path} {d : Doc} : ConformsObj s q d → ConformsElem s q d
  | scalar {q : Path} {d : Doc} {t : Table} {c : Column} :
      s.find? (fun u => u.path == q) = some t →
      t.columns = [c] → c.name = "value" →
      MatchesField s c.field d → ConformsElem s q d

end

/-- Every document of the corpus is described by the schema. The root table is
    the one at the empty path, which is where `inferCorpus` starts its walk. -/
def Conforms (s : Schema) (ds : List Doc) : Prop :=
  ∀ d ∈ ds, ConformsObj s [] d

/-- One schema is below another when every column sits at a type no wider and
    is no more optional. The table structure is not compared: it is forced by
    the shape of the documents and the markings, not chosen. -/
def Schema.le (a b : Schema) : Prop :=
  ∀ t ∈ a, ∃ u ∈ b, u.path = t.path ∧
    ∀ c ∈ t.columns, ∃ d ∈ u.columns, d.name = c.name ∧
      Ty.le c.field.ty d.field.ty ∧
      (c.field.nullable = true → d.field.nullable = true)

end Tatami
