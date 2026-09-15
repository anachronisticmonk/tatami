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
def moduleName (root : String) (p : Path) : String :=
  match Path.names p with
  | [] => root
  | segs => capitalize (String.intercalate "_" (segs.map mangle))

/-- The root table's name: the configured one, mangled like any other name so
    that it is always a legal module name, or `Root` when none was given. -/
def rootModuleName : Option String → String
  | some n => capitalize (mangle n)
  | none => "Root"

/-- A table's name, lowercased: the stem its key column, its file and its
    `of_` lookup are all built from. Distinct module names give distinct
    stems, because a module name always begins with a capital. -/
def idTypeName (root : String) (p : Path) : String :=
  match (moduleName root p).toList with
  | c :: cs => String.ofList (c.toLower :: cs)
  | [] => "root"

/-- The lookup a collection's rows carry: every row whose `parent_id` is the
    given key. It is declared in the *child*, because that is where the rows
    and the `parent_id` column live; the parent's accessor delegates to it.

    `get` keys on `id`, this keys on `parent_id`, and the child owns both. The
    parent owns neither, which is why it cannot answer the question itself. -/
def childLookupName (root : String) (parent : Path) : String := "of_" ++ idTypeName root parent

/-- Generated columns, which a document member must not collide with. -/
def parentColumn : String := "parent_id"
def indexColumn : String := "idx"
def keyColumn : String := "key"

def tyExprOf (root : String) : Ty → TyExpr
  | .bot => .unit
  | .int => .int
  | .float => .float
  | .uuid => .named "uuid"
  | .str => .string
  | .bool => .bool
  | .ref p => .qualified (moduleName root p) "id"
  | .coll p => .list (.qualified (moduleName root p) "t")   -- never a field; see below

def fieldTyExpr (root : String) (f : Field) : TyExpr :=
  let base := tyExprOf root f.ty
  if f.nullable then .option base else base

/-- A table's key column, named after the table so that a child's foreign key
    and the parent's primary key spell the same thing.

    If the document carried an `id` member, that is the key and keeps the type
    inference gave it. Otherwise one is minted, and a minted key is a uuid --
    there is nothing in the data to take, so uniqueness has to come from the
    generator. -/
def keyColumnName (root : String) (p : Path) : String := idTypeName root p ++ "_id"

/-- Where a column's value comes from. The emitted code only needs to know
    whether a column is the key; the shredder needs to know all four, because
    each is filled from somewhere different. -/
inductive ColKind where
  | key                     -- the document's `id`, or one minted for it
  | parent                  -- the key of the table these rows sit in
  | position                -- the index in the array, or the map entry's name
  | member (source : String)  -- a member of the document, by its JSON name
  deriving Repr, DecidableEq

/-- A column as it is actually emitted.

    `ty` is `.ref p` for a key into table `p`; what that is *stored* as depends
    on `p`'s own key and so cannot be settled here. -/
structure Col where
  name : String
  ty : Ty
  nullable : Bool
  kind : ColKind
  deriving Repr

def Col.isKey (c : Col) : Bool := c.kind == .key

/-- The columns a table emits, in order: its key, then the back reference and
    position if its rows sit in a collection, then the document's own members
    with collections dropped.

    Both the OCaml modules and the SQL come from this one list, which is what
    makes their column order the same by construction rather than by care. -/
def layoutOf (root : String) (t : Table) : Except Error (List Col) := do
  let keyName := keyColumnName root t.path
  let positionColumn := if t.keyed then keyColumn else indexColumn

  -- the document's own `id` is the key if it has one; otherwise mint a uuid
  let docKey := t.columns.find? (fun c => c.name == "id")
  let keyTy : Ty ← match docKey with
    | none => pure .uuid
    | some c =>
        if c.field.nullable then
          throw (.unusableKey (Path.toString t.path) "sometimes absent or null")
        else match c.field.ty with
          | .ref _ => throw (.unusableKey (Path.toString t.path) "an object")
          | .coll _ => throw (.unusableKey (Path.toString t.path) "an array")
          | .bot => throw (.unusableKey (Path.toString t.path) "never given a value")
          | ty => pure ty

  let mut cols : List Col := [{ name := keyName, ty := keyTy, nullable := false, kind := .key }]
  match t.parent with
  | some pp =>
      cols := cols ++
        [ { name := keyColumnName root pp, ty := .ref pp, nullable := false, kind := .parent }
        , { name := positionColumn, ty := if t.keyed then .str else .int
          , nullable := false, kind := .position } ]
  | none => pure ()

  let generated : List String :=
    [keyName, "get", "t", "id"]
    ++ (match t.parent with
        | some pp => [keyColumnName root pp, positionColumn, childLookupName root pp]
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
    | ty => cols := cols ++
        [{ name := name, ty := ty, nullable := c.field.nullable, kind := .member c.name }]
  return cols

def genModule (root : String) (t : Table) : Except Error Module := do
  let self := moduleName root t.path
  -- where a row source would be: reaching a row is a hole, reading one is not
  let hole (what : String) : Expr :=
    .app (.var "failwith") [.str s!"{self}.{what}: no row source"]
  let cols ← layoutOf root t

  -- a reference is the key itself, not the row: `P.get` is where the lookup
  -- happens, and it is also what lets the schema reader see it is a key
  let tyOf (c : Col) : TyExpr :=
    let base : TyExpr :=
      match c.ty with
      | .ref p => .qualified (moduleName root p) "id"
      | ty => tyExprOf root ty
    if c.nullable then .option base else base

  let fields : List RecField := cols.map fun c => { name := c.name, ty := tyOf c }
  let accessors : List Decl := cols.map fun c => .value c.name (.arrow (.named "t") (tyOf c))
  let bodies : List Decl := cols.map fun c => .letValue c.name ["r"] (.field (.var "r") c.name)

  let lookup : List Decl := match t.parent with
    | some pp =>
        [ .value (childLookupName root pp)
            (.arrow (.qualified (moduleName root pp) "id") (.list (.named "t"))) ]
    | none => []
  let lookupImpl : List Decl := match t.parent with
    | some pp => [ .letValue (childLookupName root pp) ["_"] (hole (childLookupName root pp)) ]
    | none => []

  -- `uuid` is not an OCaml type; it is a name for `string` that says what the
  -- column holds, and the schema reader and the DDL both read it
  let usesUuid := cols.any fun c => c.ty == .uuid
  let uuidAlias : List Decl := if usesUuid then [ .typeAlias "uuid" .string ] else []
  let keyTy : TyExpr := match cols.head? with
    | some c => tyOf c
    | none => .named "uuid"
  return {
    name := self
    decls := uuidAlias ++
      [ .abstractType "t"
      , .abstractType "id"
      , .value "get" (.arrow .id (.named "t")) ] ++ lookup ++ accessors
    impl := uuidAlias ++
      [ .typeAlias "id" keyTy
      , .recordType "t" fields
      , .letValue "get" ["_"] (hole "get") ] ++ lookupImpl ++ bodies
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
def genRaw (root : String) (s : Schema) : Except Error File := do
  let mut mods : List Module := []
  for t in orderTables s do
    mods := mods ++ [← genModule root t]
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

def gen (root : String) (s : Schema) : Except Error File :=
  match genRaw root s with
  | .error e => .error e
  | .ok f => certify f

end Tatami
