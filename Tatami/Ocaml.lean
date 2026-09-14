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
  deriving Repr, Inhabited

/-- Expressions, only as far as the emitted bodies reach: a projection, a
    call into another module, and the placeholder standing where a row source
    would be. Nothing here can compute. -/
inductive Expr where
  | var   : String → Expr             -- r
  | field : Expr → String → Expr      -- r.a
  | qual  : String → String → Expr    -- B.get
  | str   : String → Expr             -- "..."
  | app   : Expr → List Expr → Expr   -- f x y
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
