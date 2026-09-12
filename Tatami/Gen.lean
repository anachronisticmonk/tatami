import Tatami.Error
import Tatami.Path
import Tatami.Schema
import Tatami.Ocaml
import Tatami.Mangle

namespace Tatami

/- Schema to output language, following the design note's correspondence
   (§2.1, Step 4): a table becomes a module, a row becomes a value of type
   `t`, a column becomes a record field, the primary key becomes an abstract
   `id`, a foreign key becomes a field holding another module's `id`, joining
   on it becomes an accessor function, and a nullable column becomes an
   `option` field.

   Repeated substructures are the one place the note states a rule without
   showing it. It says they are normalized into separate relations linked by
   generated keys, so an array becomes a table whose rows carry a key back to
   the parent and an ordering index. The parent gets no column -- there is no
   single key to hold -- only an accessor returning a list. -/

private def capitalize (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: cs => String.ofList (c.toUpper :: cs)

/-- A module is named for the member names along the path of its table, so
    distinct tables get distinct names: paths are unique, `mangle` is
    injective, and it escapes `_` so a literal underscore in a member name
    cannot be mistaken for the separator. The element marker contributes no
    name -- an array's element table is named for the member holding it. -/
def moduleName (p : Path) : String :=
  match Path.names p with
  | [] => "Root"
  | segs => capitalize (String.intercalate "_" (segs.map mangle))

/-- Generated columns, which a document member must not collide with. -/
def parentColumn : String := "parent_id"
def indexColumn : String := "idx"
def keyColumn : String := "key"

def tyExprOf : Ty → TyExpr
  | .bot => .unit
  | .int => .int
  | .float => .float
  | .str => .string
  | .bool => .bool
  | .ref p => .qualified (moduleName p) "id"
  | .coll p => .list (.qualified (moduleName p) "t")   -- never a field; see below

def fieldTyExpr (f : Field) : TyExpr :=
  let base := tyExprOf f.ty
  if f.nullable then .option base else base

def genModule (t : Table) : Except Error Module := do
  let self := moduleName t.path
  -- a type from another module needs qualifying; one from this module does not
  let ref (p : Path) (n : String) : TyExpr :=
    if moduleName p == self then (if n == "id" then .id else .named n)
    else .qualified (moduleName p) n
  let positionColumn := if t.keyed then keyColumn else indexColumn
  let mut fields : List RecField := [{ name := "id", ty := .id }]
  -- rows that sit in a collection carry a key back and their position in it
  match t.parent with
  | some pp =>
      let idTy := ref pp "id"
      let posTy : TyExpr := if t.keyed then .string else .int
      fields := fields ++
        [ { name := parentColumn, ty := idTy }
        , { name := positionColumn, ty := posTy } ]
  | none => pure ()
  let mut accessors : List Decl := []
  for c in t.columns do
    let name := mangle c.name
    if name == "id" then throw (.reservedColumnName c.name "id")
    if t.parent.isSome && (name == parentColumn || name == positionColumn) then
      throw (.reservedColumnName c.name name)
    match c.field.ty with
    | .coll p =>
        -- no column: the elements point back here, so the parent holds nothing
        if name == "get" then throw (.reservedAccessorName c.name)
        accessors := accessors ++
          [ .value name (.arrow (.named "t") (.list (ref p "t"))) ]
    | .ref p =>
        if name == "get" then throw (.reservedAccessorName c.name)
        fields := fields ++ [{ name := name, ty := if c.field.nullable then .option (ref p "id") else ref p "id" }]
        let target : TyExpr := ref p "t"
        accessors := accessors ++
          [ .value name (.arrow (.named "t")
              (if c.field.nullable then .option target else target)) ]
    | _ =>
        fields := fields ++ [{ name := name, ty := fieldTyExpr c.field }]
  return {
    name := moduleName t.path
    decls :=
      [ .abstractType "id"
      , .recordType "t" fields
      , .value "get" (.arrow .id (.named "t")) ] ++ accessors
  }

/-- Exposed, with `certify`, so `Proofs.Wellformed` can invert `gen`. -/
def genRaw (s : Schema) : Except Error File := do
  let mut mods : List Module := []
  for t in s do
    mods := mods ++ [← genModule t]
  let names := mods.map (·.name)
  for n in names do
    if (names.filter (· == n)).length > 1 then throw (.moduleNameClash n)
  -- a reference between two different modules that runs both ways makes the
  -- group cyclic; a table that only points at itself does not
  let crossModule := s.any fun t =>
    match t.parent with
    | some pp => moduleName pp != moduleName t.path
    | none => false
  return { recursive := crossModule, modules := mods }

/-- The generator checks its own output before handing it back, and refuses a
    file that repeats a name rather than emitting one that will not compile.

    The checks in `genModule` catch a member colliding with a *generated*
    name and say so plainly; this catches two members colliding with each
    other. Inference cannot produce that -- `checkDistinct` rejects a repeated
    member and `mangle` is injective -- but `gen` is total on `Schema`, so
    without the check the guarantee would hold only of schemas inference
    happens to build. It is also what lets `gen_wellFormed` be proved without
    appealing to `mangle_injective`. -/
def certify (f : File) : Except Error File :=
  if f.okB then .ok f else .error (.illFormedSignature (f.badModule.getD "the file"))

def gen (s : Schema) : Except Error File :=
  match genRaw s with
  | .error e => .error e
  | .ok f => certify f

end Tatami
