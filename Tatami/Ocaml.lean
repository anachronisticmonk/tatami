namespace Tatami

/-- The output language.

    Not an embedding of OCaml: it expresses only the declarations the design
    note's generated signature contains (§2.1, Step 3), and no expressions at
    all. Its purpose is to give the generator a structured codomain, so that
    properties of the emitted code are statable about data rather than about
    a string.

    It grows one construct at a time as the input fragment grows. At this
    stage a flat object needs no list type and no module references, so it
    has neither. -/

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

structure RecField where
  name : String
  ty : TyExpr
  deriving Repr

inductive Decl where
  | abstractType : String → Decl
  | recordType   : String → List RecField → Decl
  | value        : String → TyExpr → Decl
  deriving Repr

structure Module where
  name : String
  decls : List Decl
  deriving Repr

structure File where
  /-- true when the modules refer to one another in a cycle, which an array
      always creates: the parent reaches the elements, the elements carry a
      key back to the parent -/
  recursive : Bool
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
