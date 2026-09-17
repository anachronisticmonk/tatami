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

/-- What a table's key is stored as.

    The document's own `id` is the key if it has one, and keeps the type
    inference gave it; otherwise one is minted, and a minted key is a uuid.

    Separated from `layoutOf` because a *reference* to this table needs the
    same answer, and the two must not be able to disagree: a foreign key is
    stored as whatever the key it points at is stored as, or the load fails
    on a type mismatch the schema never admitted to. -/
def keyTyOf (t : Table) : Except Error Ty :=
  match t.columns.find? (fun c => c.name == "id") with
  | none => pure .uuid
  | some c =>
      if c.field.nullable then
        throw (.unusableKey (Path.toString t.path) "sometimes absent or null")
      else match c.field.ty with
        | .ref _ => throw (.unusableKey (Path.toString t.path) "an object")
        | .coll _ => throw (.unusableKey (Path.toString t.path) "an array")
        | .bot => throw (.unusableKey (Path.toString t.path) "never given a value")
        | ty => pure ty

/-- What a column is stored as, once a key has been followed to its target.

    `Col.ty` leaves a key as `.ref p`: what `p`'s key is stored as is a fact
    about `p` and not about the column holding it, so `layoutOf`, which sees
    one table, cannot settle it. A DDL and a loader both need it settled, so
    it is done here, once, against the whole schema -- rather than twice,
    downstream, with two chances to disagree. -/
def storageTy (s : Schema) : Ty → Ty
  | .ref p =>
      match s.find? (fun t => t.path == p) with
      | some t => (keyTyOf t).toOption.getD .uuid
      | none => .uuid
  | ty => ty

/-- The names the generator puts in a module of its own accord. A member
    mangling to one of these cannot become a column: it would collide. -/
def generatedNames (nm : Naming) (t : Table) : List String :=
  [idColumn, "get", "make", "t", "id"]
  ++ (match t.parent with
      | some pp => [ keyColumnName nm pp
                   , if t.keyed then keyColumn else indexColumn
                   , childLookupName nm pp ]
      | none => [])

/-- The columns that come from the table's position rather than its contents:
    its key, and -- when its rows sit in a collection -- the back reference and
    the position within that collection. -/
def baseCols (nm : Naming) (t : Table) (keyTy : Ty) : List Col :=
  { name := idColumn, ty := keyTy, nullable := false, kind := .key } ::
  (match t.parent with
   | some pp =>
       [ { name := keyColumnName nm pp, ty := .ref pp, nullable := false, kind := .parent }
       , { name := if t.keyed then keyColumn else indexColumn
         , ty := if t.keyed then .str else .int, nullable := false, kind := .position } ]
   | none => [])

/-- What one member of the document contributes to the layout, which is a
    column or nothing at all.

    `none` twice over, for different reasons: a member called `id` was
    consumed as the key above, and an array contributes no column here -- the
    elements carry the key back, and the accessor that finds them is `of_` in
    their module, where the rows and the key are.

    Its own definition rather than the body of a loop over a mutable list, so
    that `Proofs.Tree` can say which member a column came from. -/
def memberCol (generated : List String) (c : Column) : Except Error (Option Col) :=
  if c.name == idColumn then pure none
  else
    let name := mangle c.name
    if generated.contains name then throw (.reservedColumnName c.name name)
    else match c.field.ty with
      | .coll _ => pure none
      | ty => pure (some { name := name, ty := ty
                         , nullable := c.field.nullable, kind := .member c.name })

/-- The columns a table emits, in order: its key, then the back reference and
    position if its rows sit in a collection, then the document's own members
    with collections dropped.

    Both the OCaml modules and the SQL come from this one list, which is what
    makes their column order the same by construction rather than by care. -/
def layoutOf (nm : Naming) (t : Table) : Except Error (List Col) := do
  let keyTy ← keyTyOf t
  let members ← t.columns.mapM (memberCol (generatedNames nm t))
  return baseCols nm t keyTy ++ members.filterMap id

/-- An identifier, as SQL spells one.

    Quoted, always. An unquoted identifier is folded to lower case, and a
    mangled name is not always lower case -- a JSON member `Name` becomes the
    OCaml field `f__Name`, which unquoted would reach the database as
    `f__name` and stop matching the name every other reader uses. Quoting
    costs nothing where the name was already lower case, which is why it can
    be done unconditionally rather than only where it is needed. -/
def quoteIdent (n : String) : String := "\"" ++ n ++ "\""

/-- A column's storage, in SQL.

    The same eight cases as `tyExprOf`, read into the other language. A uuid
    is a uuid here and a `string` in OCaml, which is not an inconsistency: the
    database has a type for it and OCaml has not, so each says as much as it
    can. -/
def sqlType : Ty → String
  | .int => "integer"
  | .float => "double precision"
  | .uuid => "uuid"
  | .str => "text"
  | .bool => "boolean"
  -- observed, but never with a value: nothing constrains it, and text holds
  -- whatever turns up when one finally does
  | .bot => "text"
  -- neither survives `storageTy`, which follows a key to what it is stored
  -- as, and `layoutOf`, which drops collections
  | .ref _ => "text"
  | .coll _ => "text"

/-- `CREATE TABLE`, off the same list the modules come from.

    So the table and the module cannot disagree about what the columns are or
    what order they are in: both are `layoutOf`, read into two languages.
    `NOT NULL` appears exactly where the `.mli` does not say `option`, for the
    same reason and from the same field. -/
def ddlOf (s : Schema) (nm : Naming) (t : Table) : String :=
  let cols := (layoutOf nm t).toOption.getD []
  let line (c : Col) : String :=
    s!"  {quoteIdent c.name} {sqlType (storageTy s c.ty)}"
      ++ (if c.nullable then "" else " not null")
  let body := String.intercalate ",\n" (cols.map line)
  let key := ((cols.find? Col.isKey).map (·.name)).getD idColumn
  s!"create table {quoteIdent (idTypeName nm t.path)} (\n{body},\n  primary key ({quoteIdent key})\n)"

/-- The references, restated in the database's vocabulary, and an index on
    each.

    Held back from `ddlOf` rather than declared with the columns: validating a
    reference per row while millions are loading is the load's cost, and
    applied afterwards they are checked once, in bulk. A join across the
    nesting follows these, so an unindexed key would make a three-hop join
    three sequential scans. -/
def constraintsOf (nm : Naming) (t : Table) : List String :=
  let tbl := idTypeName nm t.path
  ((layoutOf nm t).toOption.getD []).flatMap fun c =>
    match c.ty with
    | .ref p =>
        [ s!"alter table {quoteIdent tbl} add constraint {quoteIdent (tbl ++ "_" ++ c.name ++ "_fkey")} foreign key ({quoteIdent c.name}) references {quoteIdent (idTypeName nm p)} ({quoteIdent idColumn})"
        , s!"create index {quoteIdent (tbl ++ "_" ++ c.name ++ "_idx")} on {quoteIdent tbl} ({quoteIdent c.name})" ]
    | _ => []

/-- A column's type as it appears in a signature.

    A reference is the key itself, not the row: `P.get` is where the lookup
    happens, and it is also what lets the schema reader see it is a key.

    Lifted out of `genModule` so that `Proofs.Tree` can name it: the
    correspondence between a `ref` column and the accessor it becomes is
    stated of this function. -/
def colTyExpr (nm : Naming) (c : Col) : TyExpr :=
  let base : TyExpr :=
    match c.ty with
    | .ref p => .qualified (moduleName nm p) "id"
    | ty => tyExprOf nm ty
  if c.nullable then .option base else base

def genModule (nm : Naming) (t : Table) : Except Error Module := do
  let self := moduleName nm t.path
  -- where a row source would be: reaching a row is a hole, reading one is not
  let hole (what : String) : Expr :=
    .app (.var "failwith") [.str s!"{self}.{what}: no row source"]
  let cols ← layoutOf nm t

  let tyOf (c : Col) : TyExpr := colTyExpr nm c

  let fields : List RecField := cols.map fun c => { name := c.name, ty := tyOf c }
  let accessors : List Decl := cols.map fun c => .value c.name (.arrow (.named "t") (tyOf c))
  let bodies : List Decl := cols.map fun c => .letValue c.name ["r"] (.field (.var "r") c.name)

  -- a row is built once and changed by copy: `t` is abstract, so `make` is the
  -- only way to have one at all, and a setter hands back a new row rather than
  -- altering a shared one
  let makeTy : TyExpr := cols.foldr (fun c rest => .labelled c.name (tyOf c) rest) (.named "t")
  let maker : Decl := .value "make" makeTy
  let makerImpl : Decl :=
    .letValue "make" (cols.map fun c => "~" ++ c.name) (.record (cols.map (·.name)))
  let setters : List Decl := cols.map fun c =>
    .value ("set_" ++ c.name) (.arrow (.named "t") (.arrow (tyOf c) (.named "t")))
  let setterImpls : List Decl := cols.map fun c =>
    .letValue ("set_" ++ c.name) ["r", "v"] (.update (.var "r") c.name (.var "v"))

  let lookup : List Decl := match t.parent with
    | some pp =>
        [ .value (childLookupName nm pp)
            (.arrow (.qualified (moduleName nm pp) "id") (.list (.named "t"))) ]
    | none => []
  let lookupImpl : List Decl := match t.parent with
    | some pp => [ .letValue (childLookupName nm pp) ["_"] (hole (childLookupName nm pp)) ]
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
      -- transparent, unlike `t`: a foreign key is typed `Parent.id` so the
      -- schema reader can see it is one, and a row cannot be built or looked
      -- up unless a key of that type can be obtained from the parent row
      , .typeAlias "id" keyTy
      , maker
      , .value "get" (.arrow .id (.named "t")) ] ++ lookup ++ accessors ++ setters
    impl := uuidAlias ++
      [ .typeAlias "id" keyTy
      , .recordType "t" fields
      , makerImpl
      , .letValue "get" ["_"] (hole "get") ] ++ lookupImpl ++ bodies ++ setterImpls
  }

/-- The runtime's name for a storage type.

    One name picks the reader, the binder and the neutral value -- `Json.int`,
    `Bind.int`, `Neutral.int` -- so a column cannot be read as one type and
    bound as another. -/
def tyName : Ty → String
  | .int => "int"
  | .float => "float"
  | .uuid => "uuid"
  | .str => "string"
  | .bool => "bool"
  -- observed, but never with a value: there is nothing to read or bind
  | .bot => "unit"
  -- neither survives `storageTy` and `layoutOf`; see `sqlType`
  | .ref _ => "string"
  | .coll _ => "string"

/-- One table's loader: a document in, a row of bound values out.

    `make` takes what the document carries. The three columns it does not --
    the key, the back reference, the position -- go in neutral and are stamped
    by the setters, which is the same split `ColKind` already makes. So the
    loader decides nothing the layout had not decided: read `kind`, and the
    call to write is determined.

    The getters read the row back in the layout's order, which is the order
    `ddlOf` declares the columns in, so the values and the `insert` cannot
    disagree about which column is which.

    Emitted without a signature -- see `Module.implOnly`. -/
def genLoader (s : Schema) (nm : Naming) (t : Table) : Except Error Module := do
  let cols ← layoutOf nm t
  let mod := moduleName nm t.path
  -- the storage type, with the key followed to what it is stored as
  let sty (c : Col) : String := tyName (storageTy s c.ty)
  -- a nullable column is read, bound and stamped one option deeper
  let suf (c : Col) : String := if c.nullable then "_opt" else ""

  let arg (c : Col) : String × Expr :=
    match c.kind with
    | .member src =>
        match c.ty with
        -- the member is an object, and an object became its own table: the
        -- column holds that table's key, which is *inside* the object.
        -- Reading the member itself would typecheck -- a key is a string or an
        -- int like any other column -- and fail on the first document.
        | .ref _ =>
            (c.name, .app (.qual "Json" (sty c ++ suf c))
                       [.app (.qual "Json" ("obj" ++ suf c)) [.var "doc", .str src], .str idColumn])
        | _ => (c.name, .app (.qual "Json" (sty c ++ suf c)) [.var "doc", .str src])
    | _ => (c.name, .qual "Neutral" (sty c ++ suf c))
  let built : Expr := .labelledApp (.qual mod "make") (cols.map arg)

  -- the engine carries all three as bound values: it does not know what any
  -- table's key is stored as, and a position is a string under a map marking
  -- and an integer under an array. The layout knows, so the conversion back
  -- happens here.
  let stamp (c : Col) (rest : Expr) : Expr :=
    let v : Expr := match c.kind with
      | .key => .app (.qual "Unbind" (sty c)) [.var "self"]
      | .parent => .app (.qual "Unbind" (sty c)) [.var "parent"]
      | .position => .app (.qual "Unbind" (sty c)) [.var "pos"]
      | .member _ => .var "r"
    .letIn "r" (.app (.qual mod ("set_" ++ c.name)) [.var "r", v]) rest

  let derived := cols.filter fun c => match c.kind with | .member _ => false | _ => true
  let bound : Expr :=
    .list (cols.map fun c => .app (.qual "Bind" (sty c ++ suf c)) [.app (.qual mod c.name) [.var "r"]])

  -- a root has no back reference and no position, so nothing would use them
  let unused : List String :=
    (if cols.any (fun c => match c.kind with | .parent => true | _ => false) then [] else ["parent"])
    ++ (if cols.any (fun c => match c.kind with | .position => true | _ => false) then [] else ["pos"])
  let body : Expr :=
    unused.foldr (fun n rest => .letIn "_" (.var n) rest)
      (.letIn "r" built (derived.foldr stamp bound))

  -- always read, never minted here. A document that carries no `id` is given
  -- one by the engine before any of this runs, because a minted key is read
  -- twice -- once for the row itself, once for the reference column pointing
  -- at it -- and minting at each read would produce two different keys for
  -- one row. `Loader.mints` says which tables that applies to.
  let keyTy := ((cols.find? Col.isKey).map sty).getD "uuid"
  let keyBody : Expr :=
    .app (.qual "Bind" keyTy) [.app (.qual "Json" keyTy) [.var "doc", .str idColumn]]

  return {
    name := mod ++ "_row"
    decls := []
    implOnly := true
    impl :=
      [ .letValue "table" [] (.str (idTypeName nm t.path))
      , .letValue "columns" [] (.list (cols.map fun c => Expr.str c.name))
      , .letValue "key" ["~doc"] keyBody
      , .letValue "row" ["~self", "~parent", "~pos", "~doc"] body ]
  }

/-- The tables a unit names: its parent, for the foreign key, and the target
    of every `ref` column. -/
def depsOf (t : Table) : List Path :=
  (match t.parent with | some pp => [pp] | none => []) ++
  t.columns.filterMap fun c => match c.field.ty with | .ref p => some p | _ => none

-- not `private`: `Proofs.Tree` reasons about what `orderTables` keeps
def orderGo : Nat → List Table → List Table → List Table
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

/-- The registry: everything the engine asks about a table, answered by name.

    The engine walks documents and batches rows, and has no table name in it.
    So every question it asks -- what does this table hold collections of,
    what does it point at, how do I read one of its rows -- is answered here,
    and here is generated. Adding a table to the corpus adds a case; it does
    not change the engine.

    Every `match` has a default, so the registry is total: asking about a
    table that does not exist is answered, not a crash. -/
def genRegistry (s : Schema) (nm : Naming) : Except Error Module := do
  let ordered := orderTables s
  let nameOf (t : Table) : String := idTypeName nm t.path
  let rowMod (t : Table) : String := moduleName nm t.path ++ "_row"

  -- what a table holds collections of: every table whose rows sit in one of
  -- its members, under the member holding them
  let kidsOf (t : Table) : List (String × Table) :=
    ordered.filterMap fun c =>
      match c.parent with
      | some pp =>
          if pp == t.path then ((Path.names c.path).getLast?).map (fun m => (m, c)) else none
      | none => none

  -- what a table points at: a member that was an object and became a table
  let refsOf (t : Table) : List (String × Table) :=
    t.columns.filterMap fun col =>
      match col.field.ty with
      | .ref p => (ordered.find? (fun c => c.path == p)).map fun c => (col.name, c)
      | _ => none

  let byName (f : Table → Expr) (dflt : Expr) : Expr :=
    .matchStr (.var "t") (ordered.map fun t => (nameOf t, f t)) dflt
  let strs (xs : List String) : Expr := .list (xs.map Expr.str)

  return {
    name := "Loader"
    decls := []
    implOnly := true
    impl :=
      -- in the order `orderTables` gives, which is a topological sort of the
      -- graph the foreign keys run along: a table always follows the tables it
      -- points into, so this is the load order
      [ .letValue "tables" [] (strs (ordered.map nameOf))
      , .letValue "root" []
          (.str (((ordered.find? (fun t => t.path.isEmpty)).map nameOf).getD ""))
      , .letValue "ddl" [] (.list (ordered.map fun t => Expr.str (ddlOf s nm t)))
      , .letValue "constraints" []
          (.list (ordered.flatMap fun t => (constraintsOf nm t).map Expr.str))
      , .letValue "columns" ["t"] (byName (fun t => .qual (rowMod t) "columns") (.list []))
      -- rows keyed by a member name rather than positioned by an index
      , .letValue "keyed" ["t"] (byName (fun t => .var (if t.keyed then "true" else "false")) (.var "false"))
      -- the document carries no `id`, so one is created for it
      , .letValue "mints" ["t"]
          (byName (fun t => .var (if (t.columns.find? (fun c => c.name == idColumn)).isNone
                                  then "true" else "false")) (.var "false"))
      , .letValue "child_members" ["t"] (byName (fun t => strs ((kidsOf t).map (fun k => k.1))) (.list []))
      , .letValue "child_tables" ["t"] (byName (fun t => strs ((kidsOf t).map (fun k => nameOf k.2))) (.list []))
      , .letValue "ref_members" ["t"] (byName (fun t => strs ((refsOf t).map (fun k => k.1))) (.list []))
      , .letValue "ref_tables" ["t"] (byName (fun t => strs ((refsOf t).map (fun k => nameOf k.2))) (.list []))
      , .letValue "key" ["t", "~doc"]
          (byName (fun t => .labelledApp (.qual (rowMod t) "key") [("doc", .var "doc")])
            (.qual "Pgx.Value" "null"))
      , .letValue "row" ["t", "~self", "~parent", "~pos", "~doc"]
          (byName (fun t => .labelledApp (.qual (rowMod t) "row")
            [("self", .var "self"), ("parent", .var "parent"),
             ("pos", .var "pos"), ("doc", .var "doc")]) (.list []))
      ]
  }

/-- The last step of `genRaw`: refuse a file that repeats a module name,
    naming the first one that repeats.

    Its own definition rather than a tail of the `do` block, so that a proof
    can case on it without first having to see through the block's binders. -/
def noClash (mods : List Module) : Except Error File :=
  let names := mods.map (·.name)
  match names.find? (fun n => (names.filter (· == n)).length > 1) with
  | some n => .error (.moduleNameClash n)
  | none => .ok { modules := mods }

/-- Exposed, with `certify`, so `Proofs.Wellformed` can invert `gen`. -/
def genRaw (nm : Naming) (s : Schema) : Except Error File := do
  let ordered := orderTables s
  -- three `mapM`s and an append rather than a loop over a mutable list: the
  -- result is then a function of `ordered` that `Proofs.Tree` can take apart,
  -- which a `for` accumulating into `mut` is not. The order and the
  -- first-error behaviour are the same.
  let units ← ordered.mapM (genModule nm)
  -- after every module, not beside its own: a loader names the module it
  -- loads, and the modules are already in an order where nothing names a unit
  -- not yet compiled
  let loaders ← ordered.mapM (genLoader s nm)
  -- last of all: it names every loader
  let registry ← genRegistry s nm
  noClash (units ++ loaders ++ [registry])

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
