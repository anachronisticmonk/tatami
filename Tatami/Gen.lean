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

/-- What the tables are called.

    A table's name is derived from its path -- the member names along it,
    joined -- unless the user supplied one. The root has no member names, so
    its name is always supplied or defaulted; every other table can be named
    for the same reason, which is that a path says where a table came from
    and not what it is.

    A name is looked up by the table's own path, `.runs[]`. The path of the
    member holding it, `.runs`, is accepted too: a member is a collection or
    an object and never both, so the two spellings cannot name different
    tables. -/
structure Naming where
  /-- the root table's module name, already mangled and capitalized -/
  root : String
  /-- names the user gave, by the path of the table each one names -/
  tables : List (Path × String) := []
  deriving Inhabited

def Naming.find? (nm : Naming) (p : Path) : Option String :=
  match nm.tables.find? (fun e => e.1 == p) with
  | some (_, n) => some n
  | none =>
      -- the member holding a collection names the collection's table
      match p.reverse with
      | Seg.elem :: rest | Seg.entry :: rest =>
          (nm.tables.find? (fun e => e.1 == rest.reverse)).map (·.2)
      | _ => none

/-- A module is named for the member names along the path of its table, so
    distinct tables get distinct names: paths are unique, `mangle` is
    injective, and it escapes `_` so a literal underscore in a member name
    cannot be mistaken for the separator. The element marker contributes no
    name -- an array's element table is named for the member holding it. -/
def moduleName (nm : Naming) (p : Path) : String :=
  match nm.find? p with
  | some n => capitalize (mangle n)
  | none =>
    match Path.names p with
    | [] => nm.root
    | segs => capitalize (String.intercalate "_" (segs.map mangle))

/-- The root table's name: the configured one, mangled like any other name so
    that it is always a legal module name, or `Root` when none was given. -/
def rootModuleName : Option String → String
  | some n => capitalize (mangle n)
  | none => "Root"

/-- A table's name, lowercased: the stem its key column, its file and its
    `of_` lookup are all built from. Distinct module names give distinct
    stems, because a module name always begins with a capital. -/
def idTypeName (nm : Naming) (p : Path) : String :=
  match (moduleName nm p).toList with
  | c :: cs => String.ofList (c.toLower :: cs)
  | [] => "root"

/-- The lookup a collection's rows carry: every row whose `parent_id` is the
    given key. It is declared in the *child*, because that is where the rows
    and the `parent_id` column live; the parent's accessor delegates to it.

    `get` keys on `id`, this keys on `parent_id`, and the child owns both. The
    parent owns neither, which is why it cannot answer the question itself. -/
def childLookupName (nm : Naming) (parent : Path) : String := "of_" ++ idTypeName nm parent

/-- Generated columns, which a document member must not collide with. -/
def parentColumn : String := "parent_id"
def indexColumn : String := "idx"
def keyColumn : String := "key"

/-- A table's own key column. Always `id`, whatever the table is called: the
    schema reader settles a foreign key's storage by looking up the key column
    of the table the key points into, and it finds that column by this name.
    A name that varied with the table would leave it nothing to look up.

    If the document carried an `id` member, that is the key and keeps the type
    inference gave it. Otherwise one is minted, and a minted key is a uuid --
    there is nothing in the data to take, so uniqueness has to come from the
    generator. -/
def idColumn : String := "id"

def tyExprOf (nm : Naming) : Ty → TyExpr
  | .bot => .unit
  | .int => .int
  | .float => .float
  | .uuid => .named "uuid"
  | .str => .string
  | .bool => .bool
  | .ref p => .qualified (moduleName nm p) "id"
  | .coll p => .list (.qualified (moduleName nm p) "t")   -- never a field; see below

def fieldTyExpr (nm : Naming) (f : Field) : TyExpr :=
  let base := tyExprOf nm f.ty
  if f.nullable then .option base else base

/-- The name a *child* gives its parent's key: the parent's table name with
    `_id` after it, so the column says which table it points into.

    A table's own key is `idColumn`, not this. The two once spelled the same,
    which read well but left the schema reader with no fixed name to resolve a
    key's storage by; only the reference carries the table's name now. -/
def keyColumnName (nm : Naming) (p : Path) : String := idTypeName nm p ++ "_id"

def genModule (nm : Naming) (t : Table) : Except Error Module := do
  let self := moduleName nm t.path
  let keyName := idColumn
  -- where a row source would be: reaching a row is a hole, reading one is not
  let hole (what : String) : Expr :=
    .app (.var "failwith") [.str s!"{self}.{what}: no row source"]
  let positionColumn := if t.keyed then keyColumn else indexColumn

  -- the document's own `id` is the key if it has one; otherwise mint a uuid
  let docKey := t.columns.find? (fun c => c.name == "id")
  let keyTy : TyExpr ← match docKey with
    | none => pure (.named "uuid")
    | some c =>
        if c.field.nullable then
          throw (.unusableKey (Path.toString t.path) "sometimes absent or null")
        else match c.field.ty with
          | .ref _ => throw (.unusableKey (Path.toString t.path) "an object")
          | .coll _ => throw (.unusableKey (Path.toString t.path) "an array")
          | .bot => throw (.unusableKey (Path.toString t.path) "never given a value")
          | ty => pure (tyExprOf nm ty)
  let mut usesUuid :=
    docKey.isNone || (match docKey with | some c => c.field.ty == .uuid | none => false)

  let mut fields : List RecField := [{ name := keyName, ty := keyTy }]
  let mut decls : List Decl := [ .value keyName (.arrow (.named "t") keyTy) ]
  let mut bodies : List Decl := [ .letValue keyName ["r"] (.field (.var "r") keyName) ]

  -- rows that sit in a collection carry their parent's key and their position
  match t.parent with
  | some pp =>
      let pkName := keyColumnName nm pp
      let pkTy : TyExpr := .qualified (moduleName nm pp) "id"
      let posTy : TyExpr := if t.keyed then .string else .int
      fields := fields ++ [{ name := pkName, ty := pkTy }, { name := positionColumn, ty := posTy }]
      decls := decls ++
        [ .value pkName (.arrow (.named "t") pkTy)
        , .value positionColumn (.arrow (.named "t") posTy)
        , .value (childLookupName nm pp) (.arrow pkTy (.list (.named "t"))) ]
      bodies := bodies ++
        [ .letValue pkName ["r"] (.field (.var "r") pkName)
        , .letValue positionColumn ["r"] (.field (.var "r") positionColumn)
        , .letValue (childLookupName nm pp) ["_"] (hole (childLookupName nm pp)) ]
  | none => pure ()

  let generated : List String :=
    [keyName, "get", "t", "id"]
    ++ (match t.parent with
        | some pp => [keyColumnName nm pp, positionColumn, childLookupName nm pp]
        | none => [])

  for c in t.columns do
    if c.name == "id" then continue        -- consumed as the key above
    let name := mangle c.name
    if generated.contains name then throw (.reservedColumnName c.name name)
    match c.field.ty with
    | .coll _ =>
        -- nothing here: the elements carry the key back, and the accessor that
        -- finds them is `of_` in their module, where the rows and the key are
        pure ()
    | .ref p =>
        -- the key itself, not the row: `P.get` is where the lookup happens,
        -- and it is also what lets the schema reader see this is a foreign key
        let ty : TyExpr :=
          let base : TyExpr := .qualified (moduleName nm p) "id"
          if c.field.nullable then .option base else base
        fields := fields ++ [{ name := name, ty := ty }]
        decls := decls ++ [ .value name (.arrow (.named "t") ty) ]
        bodies := bodies ++ [ .letValue name ["r"] (.field (.var "r") name) ]
    | ty =>
        if ty == .uuid then usesUuid := true
        let fty := fieldTyExpr nm c.field
        fields := fields ++ [{ name := name, ty := fty }]
        decls := decls ++ [ .value name (.arrow (.named "t") fty) ]
        bodies := bodies ++ [ .letValue name ["r"] (.field (.var "r") name) ]

  -- `uuid` is not an OCaml type; it is a name for `string` that says what the
  -- column holds, and the schema reader and the DDL both read it
  let uuidAlias : List Decl := if usesUuid then [ .typeAlias "uuid" .string ] else []
  return {
    name := self
    decls := uuidAlias ++
      [ .abstractType "t"
      , .abstractType "id"
      , .value "get" (.arrow .id (.named "t")) ] ++ decls
    impl := uuidAlias ++
      [ .typeAlias "id" keyTy
      , .recordType "t" fields
      , .letValue "get" ["_"] (hole "get") ] ++ bodies
  }

/-- The tables a unit names: its parent, for the foreign key, and the target
    of every `ref` column. -/
private def depsOf (t : Table) : List Path :=
  (match t.parent with | some pp => [pp] | none => []) ++
  t.columns.filterMap fun c => match c.field.ty with | .ref p => some p | _ => none

private def orderGo : Nat → List Table → List Table → List Table
  | 0, pending, acc => acc.reverse ++ pending
  | _, [], acc => acc.reverse
  | fuel + 1, pending, acc =>
      let done := acc.map (·.path)
      let ready := pending.filter fun t => (depsOf t).all fun d => done.contains d
      match ready with
      | [] => acc.reverse ++ pending
      | _ =>
        let rest := pending.filter fun t => !(ready.any fun r => r.path == t.path)
        orderGo fuel rest (ready.reverse ++ acc)

/-- Compilation order: a unit must follow every unit it names.

    A collection's rows name their parent, for the foreign key; a `ref` column
    names the table it points into, which is a child. So the edges run both up
    and down the document tree and a length sort is no longer enough. The
    graph is still acyclic -- a member is a `ref` or a collection, never both,
    so no two tables can name each other. -/
def orderTables (s : Schema) : Schema := orderGo s.length s []

/-- Exposed, with `certify`, so `Proofs.Wellformed` can invert `gen`. -/
def genRaw (nm : Naming) (s : Schema) : Except Error File := do
  let mut mods : List Module := []
  for t in orderTables s do
    mods := mods ++ [← genModule nm t]
  let names := mods.map (·.name)
  for n in names do
    if (names.filter (· == n)).length > 1 then throw (.moduleNameClash n)
  return { modules := mods }

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

def gen (nm : Naming) (s : Schema) : Except Error File :=
  match genRaw nm s with
  | .error e => .error e
  | .ok f => certify f

end Tatami
