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

/-- The module holding every table's key type.

    A foreign key names a type here rather than in the module it points into,
    which is what keeps the units acyclic. Without it a collection's rows
    would name their parent's `id` and the parent would name their `t`, and
    OCaml compilation units cannot be mutually recursive. -/
def idsModuleName : String := "Ids"

/-- A table's key type inside `Ids`: its module name, lowercased. Distinct
    module names give distinct type names, because a module name always
    begins with a capital. -/
def idTypeName (p : Path) : String :=
  match (moduleName p).toList with
  | c :: cs => String.ofList (c.toLower :: cs)
  | [] => "root"

/-- Every table's key type, abstract, and nothing else.

    There is deliberately no way to make one. An earlier version exposed an
    injection per table, on the reasoning that the generated implementations
    are separate compilation units and so cannot see through the abstraction.
    Nothing generated ever called one: every path that would *reach* a row is
    a hole, so no emitted body constructs a key. All it did was let a consumer
    build a foreign key naming a row that does not exist.

    So a key can be obtained only from a row, and a row only from `get` or
    `of_`, which is the honest reading of "no row source": there is no way in
    at all. Whatever fills those holes will need to construct keys, and the
    place for that is a wrapped library whose public interface omits `Ids`,
    not a naming convention. -/
def idsModule (s : Schema) : Module :=
  { name := idsModuleName
  , decls := s.map fun t => .abstractType (idTypeName t.path)
  , impl := s.map fun t => .typeAlias (idTypeName t.path) .int }

/-- The lookup a collection's rows carry: every row whose `parent_id` is the
    given key. It is declared in the *child*, because that is where the rows
    and the `parent_id` column live; the parent's accessor delegates to it.

    `get` keys on `id`, this keys on `parent_id`, and the child owns both. The
    parent owns neither, which is why it cannot answer the question itself. -/
def childLookupName (parent : Path) : String := "of_" ++ idTypeName parent

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
  if self == idsModuleName then throw (.reservedModuleName (Path.toString t.path))
  -- a type from another module needs qualifying; one from this module does not
  let ref (p : Path) (n : String) : TyExpr :=
    if moduleName p == self then (if n == "id" then .id else .named n)
    else .qualified (moduleName p) n
  -- where a row source would be. Phase 1 emits no shredder, so every way of
  -- *reaching* a row is a hole; every way of *reading* one is a projection.
  let hole (what : String) : Expr :=
    .app (.var "failwith") [.str s!"{self}.{what}: no row source"]
  let positionColumn := if t.keyed then keyColumn else indexColumn
  let lookupName : Option String := t.parent.map childLookupName
  let mut fields : List RecField := [{ name := "id", ty := .id }]
  let mut lookup : List Decl := []
  let mut lookupImpl : List Decl := []
  -- rows that sit in a collection carry a key back and their position in it
  match t.parent with
  | some pp =>
      -- the one place a unit must not name the module it points into: these
      -- rows are reached *from* their parent, so naming it would be a cycle
      let idTy : TyExpr := .qualified idsModuleName (idTypeName pp)
      let posTy : TyExpr := if t.keyed then .string else .int
      fields := fields ++
        [ { name := parentColumn, ty := idTy }
        , { name := positionColumn, ty := posTy } ]
      let nm := childLookupName pp
      lookup := [ .value nm (.arrow idTy (.list (.named "t"))) ]
      lookupImpl := [ .letValue nm ["_"] (hole nm) ]
  | none => pure ()
  let mut accessors : List Decl := []
  let mut bodies : List Decl := []
  for c in t.columns do
    let name := mangle c.name
    if name == "id" then throw (.reservedColumnName c.name "id")
    if t.parent.isSome && (name == parentColumn || name == positionColumn) then
      throw (.reservedColumnName c.name name)
    -- every column now carries an accessor, so every column can collide
    if name == "get" then throw (.reservedAccessorName c.name "get")
    -- unreachable for a schema inference built, since `mangle` escapes `_` and
    -- so can never produce `of_root`; kept because `gen` is total on `Schema`,
    -- the same reason `certify` checks the file it just built
    if lookupName == some name then throw (.reservedAccessorName c.name name)
    match c.field.ty with
    | .coll p =>
        -- no column: the elements point back here, so the parent holds nothing
        accessors := accessors ++
          [ .value name (.arrow (.named "t") (.list (ref p "t"))) ]
        -- delegate: the rows are the child's, and so is the parent_id column
        bodies := bodies ++
          [ .letValue name ["r"]
              (.app (.qual (moduleName p) (childLookupName t.path))
                    [.field (.var "r") "id"]) ]
    | .ref p =>
        fields := fields ++ [{ name := name, ty := if c.field.nullable then .option (ref p "id") else ref p "id" }]
        let target : TyExpr := ref p "t"
        accessors := accessors ++
          [ .value name (.arrow (.named "t")
              (if c.field.nullable then .option target else target)) ]
        -- following a foreign key is a projection and a `get`
        let follow : Expr :=
          if c.field.nullable then
            .app (.qual "Option" "map") [.qual (moduleName p) "get", .field (.var "r") name]
          else
            .app (.qual (moduleName p) "get") [.field (.var "r") name]
        bodies := bodies ++ [ .letValue name ["r"] follow ]
    | _ =>
        fields := fields ++ [{ name := name, ty := fieldTyExpr c.field }]
        -- the design note's `val a : Root.t -> int` / `let a r = r.a`; this is
        -- what Phase 2 rewrites into a yielding accessor
        accessors := accessors ++
          [ .value name (.arrow (.named "t") (fieldTyExpr c.field)) ]
        bodies := bodies ++ [ .letValue name ["r"] (.field (.var "r") name) ]
  return {
    name := moduleName t.path
    decls :=
      [ .typeAlias "id" (.qualified idsModuleName (idTypeName t.path))
      , .recordType "t" fields
      , .value "get" (.arrow .id (.named "t")) ] ++ lookup ++ accessors
    impl :=
      [ .typeAlias "id" (.qualified idsModuleName (idTypeName t.path))
      , .recordType "t" fields
      , .letValue "get" ["_"] (hole "get") ] ++ lookupImpl ++ bodies
  }

/-- Exposed, with `certify`, so `Proofs.Wellformed` can invert `gen`. -/
def genRaw (s : Schema) : Except Error File := do
  let mut mods : List Module := []
  for t in s do
    mods := mods ++ [← genModule t]
  let names := mods.map (·.name)
  for n in names do
    if (names.filter (· == n)).length > 1 then throw (.moduleNameClash n)
  return { modules := idsModule s :: mods }

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
