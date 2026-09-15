namespace Tatami

/-- The output language.

    Not an embedding of OCaml: it expresses only the declarations the design
    note's generated signature contains (§2.1, Step 3), and no expressions at
    all. Its purpose is to give the generator a structured codomain, so that
    properties of the emitted code are statable about data rather than about
    a string.

    It grows one construct at a time as the input fragment grows.

    Phase 1 emits implementations as well as signatures (design note §3: the
    note shows `val a : Root.t -> int` beside `let a r = r.a`), and Phase 2 is
    a *source-to-source pass over that generated code*. So the bodies have to
    be data too, or Phase 2 is string rewriting and nothing about it can be
    stated. `Expr` below is grown to exactly what those bodies need. -/

inductive TyExpr where
  | id
  | int
  | float
  | string
  | bool
  | unit
  | option : TyExpr → TyExpr
  | list   : TyExpr → TyExpr
  | named  : String → TyExpr
  | qualified : String → String → TyExpr   -- a type from another module, M.t
  | arrow  : TyExpr → TyExpr → TyExpr
  /-- `name:int -> t`. A constructor taking seven positional arguments, several
      of them `int`, is a constructor that gets called wrongly; labels are what
      make `make` safe to use. -/
  | labelled : String → TyExpr → TyExpr → TyExpr
  deriving Repr, Inhabited

/-- Expressions, only as far as the emitted bodies reach: a projection, a
    call into another module, and the placeholder standing where a row source
    would be.

    The accessors need nothing that computes. The loader does -- it builds a
    row with `make`, stamps the columns the document did not carry with the
    setters, and reads it back through the getters into a list of bound
    values. That is four more constructors and no more: a labelled
    application, because `make` is labelled and an unlabelled one would be the
    very confusion labels exist to prevent; a list, because a row of bound
    values is one; a `let`, because stamping is a sequence and nesting it
    would be unreadable; and an integer, for the neutral value a derived
    column holds until it is stamped.

    Still nothing that branches or loops. The traversal is the same for every
    schema, so it is not generated, and what is generated stays a fixed shape
    per column -- which is what keeps it checkable by reading. -/
inductive Expr where
  | var   : String → Expr             -- r
  | field : Expr → String → Expr      -- r.a
  | qual  : String → String → Expr    -- B.get
  | str   : String → Expr             -- "..."
  | int   : Int → Expr                -- 0
  | app   : Expr → List Expr → Expr   -- f x y
  /-- `f ~a:x ~b:y`. `make` is labelled, so the call that builds a row has to
      be too, or the labels guard nothing at the only place they are used. -/
  | labelledApp : Expr → List (String × Expr) → Expr
  | list  : List Expr → Expr          -- [a; b; c]
  /-- `let r = e in body`: a row is stamped one column at a time. -/
  | letIn : String → Expr → Expr → Expr
  /-- `match e with | "a" -> x | _ -> d`: the registry, which answers a
      question about a table given its name. Cases are string literals and
      there is always a default, so it is total by construction and nothing
      about it needs to be proved exhaustive. -/
  | matchStr : Expr → List (String × Expr) → Expr → Expr
  | record : List String → Expr       -- { a; b }, each field from a like-named binding
  | update : Expr → String → Expr → Expr   -- { r with a = v }
  deriving Repr, Inhabited

structure RecField where
  name : String
  ty : TyExpr
  deriving Repr

inductive Decl where
  | abstractType : String → Decl
  /-- `type id = Ids.root`: a name for a type declared elsewhere. Each unit
      gives its key type such a name, so that `Root.id` stays writable while
      the type itself lives in `Ids` and no unit depends on another for it. -/
  | typeAlias    : String → TyExpr → Decl
  | recordType   : String → List RecField → Decl
  | value        : String → TyExpr → Decl
  /-- `let a r = r.a`: an implementation. Only appears in a `.ml`. -/
  | letValue     : String → List String → Expr → Decl
  deriving Repr

structure Module where
  name : String
  /-- the `.mli` -/
  decls : List Decl
  /-- the `.ml`. Well-formedness is stated of `decls` only: the signature is
      what a consumer compiles against, and the implementation is checked by
      OCaml against it. -/
  impl : List Decl := []
  /-- emit the `.ml` and no `.mli`.

      Set for the loaders. The schema reader takes every `.mli` in the
      directory for a table and reads its `val`s as columns; a loader is not a
      table, and an `.mli` for one would show up there as a table with no
      columns. It has nothing to state anyway -- its whole content is the
      plumbing, and a signature would be a second copy of it. -/
  implOnly : Bool := false
  deriving Repr

/-- Every module the generator emits, each of which becomes one `.mli`
    compilation unit, in the order they must be compiled. -/
structure File where
  modules : List Module
  deriving Repr

/-- Distinctness of a list of names, as a `Bool` so the generator can test it.

    `Proofs.Wellformed` states well-formedness as a proposition and proves
    this implies it; the two must be read together. -/
def nodupNames : List String → Bool
  | [] => true
  | n :: ns => !ns.contains n && nodupNames ns

/-- The field names of each record type in a module, one list per record. -/
def Module.recordFieldNames (m : Module) : List (List String) :=
  m.decls.filterMap fun d => match d with
    | .recordType _ fs => some (fs.map RecField.name)
    | _ => none

/-- The names of the values a module declares. -/
def Module.valueNames (m : Module) : List String :=
  m.decls.filterMap fun d => match d with
    | .value n _ => some n
    | _ => none

def Module.okB (m : Module) : Bool :=
  m.recordFieldNames.all nodupNames && nodupNames m.valueNames

/-- Every record field, value and module name is distinct. The generator
    checks this of its own output before returning it, so that the guarantee
    holds of any schema rather than only of the ones inference produces. -/
def File.okB (f : File) : Bool :=
  nodupNames (f.modules.map Module.name) && f.modules.all Module.okB

/-- The first module that fails the check, for the diagnostic. -/
def File.badModule (f : File) : Option String :=
  (f.modules.find? fun m => !m.okB).map Module.name

end Tatami
