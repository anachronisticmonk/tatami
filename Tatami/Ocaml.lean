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

end Tatami
