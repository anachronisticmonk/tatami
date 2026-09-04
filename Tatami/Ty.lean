import Tatami.Path

namespace Tatami

/-- The type of a member.

    A nested object does not have a type of its own: the design note turns it
    into a table of its own and leaves the parent holding a key into it
    (§2.1, Step 4). `ref` is that key, and it names the table by its path.

    The design note settles the two ends of this -- a column becomes a record
    field, a nullable column an `option` field -- but not how a member seen as
    both an integer and a float should be typed. That ordering is ours: `bot`
    sits under everything, `int` under `float`, and nothing else is
    comparable. -/
inductive Ty where
  | bot     -- observed, but never with a value
  | int
  | float
  | str
  | bool
  | ref : Path → Ty      -- a nested object: a key into its table
  | coll : Path → Ty     -- an array: no column here, the elements point back
  deriving Repr, DecidableEq, BEq, Inhabited

def Ty.toString : Ty → String
  | .bot => "unknown"
  | .int => "int"
  | .float => "float"
  | .str => "string"
  | .bool => "bool"
  | .ref p => "the object at " ++ Path.toString p
  | .coll p => "the array at " ++ Path.toString p

instance : ToString Ty := ⟨Ty.toString⟩

/-- Nullability is a flag on the member, not one of the types above: the note
    treats it as a property of the column, carried into OCaml as `option`. -/
structure Field where
  ty : Ty
  nullable : Bool
  deriving Repr, Inhabited

/-- The common type of two observations, where there is one. `none` is the
    case we refuse.

    Two references at the same member always name the same table, since the
    table is named by the member's own path. -/
def Ty.join : Ty → Ty → Option Ty
  | .bot, t => some t
  | t, .bot => some t
  | .int, .int => some .int
  | .int, .float => some .float
  | .float, .int => some .float
  | .float, .float => some .float
  | .str, .str => some .str
  | .bool, .bool => some .bool
  | .ref p, .ref q => if p = q then some (.ref p) else none
  | .coll p, .coll q => if p = q then some (.coll p) else none
  | _, _ => none

def Field.join (a b : Field) : Option Field :=
  (a.ty.join b.ty).map fun t => { ty := t, nullable := a.nullable || b.nullable }

def Field.toString (f : Field) : String :=
  f.ty.toString ++ if f.nullable then " option" else ""

end Tatami
