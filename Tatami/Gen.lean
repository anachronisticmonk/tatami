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
  let mut fields : List RecField := [{ name := "id", ty := .id }]
  -- an element table's rows carry a key back to the parent and their position
  match t.parent with
  | some pp =>
      fields := fields ++
        [ { name := parentColumn, ty := .qualified (moduleName pp) "id" }
        , { name := indexColumn, ty := .int } ]
  | none => pure ()
  let mut accessors : List Decl := []
  for c in t.columns do
    let name := mangle c.name
    if name == "id" then throw (.reservedColumnName c.name "id")
    if t.parent.isSome && (name == parentColumn || name == indexColumn) then
      throw (.reservedColumnName c.name name)
    match c.field.ty with
    | .coll p =>
        -- no column: the elements point back here, so the parent holds nothing
        if name == "get" then throw (.reservedAccessorName c.name)
        accessors := accessors ++
          [ .value name (.arrow (.named "t") (.list (.qualified (moduleName p) "t"))) ]
    | .ref p =>
        if name == "get" then throw (.reservedAccessorName c.name)
        fields := fields ++ [{ name := name, ty := fieldTyExpr c.field }]
        let target : TyExpr := .qualified (moduleName p) "t"
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

def gen (s : Schema) : Except Error File := do
  let mut mods : List Module := []
  for t in s do
    mods := mods ++ [← genModule t]
  let names := mods.map (·.name)
  for n in names do
    if (names.filter (· == n)).length > 1 then throw (.moduleNameClash n)
  -- any element table makes the references cyclic
  return { recursive := s.any (fun t => t.parent.isSome), modules := mods }

end Tatami
