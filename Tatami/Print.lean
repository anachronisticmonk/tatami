import Tatami.Ocaml

namespace Tatami

/-- The one trusted step: output language to text. Structurally recursive and
    total, so it can be checked by reading. -/

def TyExpr.needsParens : TyExpr → Bool
  | .arrow _ _ => true
  | _ => false

def TyExpr.print : TyExpr → String
  | .id => "id"
  | .int => "int"
  | .float => "float"
  | .string => "string"
  | .bool => "bool"
  | .unit => "unit"
  | .named n => n
  | .qualified m n => m ++ "." ++ n
  | .option t =>
      (if t.needsParens then "(" ++ t.print ++ ")" else t.print) ++ " option"
  | .list t =>
      (if t.needsParens then "(" ++ t.print ++ ")" else t.print) ++ " list"
  | .arrow a b =>
      (if a.needsParens then "(" ++ a.print ++ ")" else a.print) ++ " -> " ++ b.print
  | .labelled n a b =>
      n ++ ":" ++ (if a.needsParens then "(" ++ a.print ++ ")" else a.print) ++ " -> " ++ b.print

/- `Expr.atom` is the same printer with parentheses where an argument
   position needs them; the two are mutual so that nesting stays structural. -/
mutual

def Expr.print : Expr → String
  | .var n => n
  | .field e f => Expr.atom e ++ "." ++ f
  | .qual m n => m ++ "." ++ n
  | .str s => "\"" ++ s ++ "\""
  | .app f args => String.intercalate " " (Expr.atom f :: Expr.atoms args)
  | .record fs => "{ " ++ String.intercalate "; " fs ++ " }"
  | .update e f v => "{ " ++ Expr.atom e ++ " with " ++ f ++ " = " ++ Expr.atom v ++ " }"

def Expr.atom : Expr → String
  | .app f args => "(" ++ String.intercalate " " (Expr.atom f :: Expr.atoms args) ++ ")"
  | .var n => n
  | .field e f => Expr.atom e ++ "." ++ f
  | .qual m n => m ++ "." ++ n
  | .str s => "\"" ++ s ++ "\""
  | .record fs => "{ " ++ String.intercalate "; " fs ++ " }"
  | .update e f v => "{ " ++ Expr.atom e ++ " with " ++ f ++ " = " ++ Expr.atom v ++ " }"

def Expr.atoms : List Expr → List String
  | [] => []
  | e :: tl => Expr.atom e :: Expr.atoms tl

end

def Decl.print : Decl → String
  | .abstractType n => s!"type {n}"
  | .typeAlias n ty => s!"type {n} = {ty.print}"
  | .recordType n fields =>
      let body := String.intercalate "; "
        (fields.map fun f => s!"{f.name} : {f.ty.print}")
      s!"type {n} = \{ {body} }"
  | .value n ty => s!"val {n} : {ty.print}"
  | .letValue n params body =>
      let ps := if params.isEmpty then "" else " " ++ String.intercalate " " params
      s!"let {n}{ps} = {body.print}"

/-- The file a module is written to. OCaml takes a unit's module name from
    its file name, capitalised, so lowercasing the module name inverts it. -/
def Module.fileName (m : Module) : String :=
  (match m.name.toList with
   | c :: cs => String.ofList (c.toLower :: cs)
   | [] => m.name) ++ ".mli"

/-- One module as one compilation unit: its declarations at the top level,
    with no enclosing `sig`, because the file itself is the signature. -/
def Module.printUnit (m : Module) : String :=
  let body := String.intercalate "\n" (m.decls.map Decl.print)
  s!"(* {m.fileName} *)\n\n{body}\n"

def Module.implFileName (m : Module) : String :=
  (match m.name.toList with
   | c :: cs => String.ofList (c.toLower :: cs)
   | [] => m.name) ++ ".ml"

def Module.printImpl (m : Module) : String :=
  let body := String.intercalate "\n" (m.impl.map Decl.print)
  s!"(* {m.implFileName} *)\n\n{body}\n"

/-- Every file, in the order they must be compiled: each module's signature
    immediately before its implementation, `Ids` first and the rest
    deepest-first, so nothing ever names a unit not yet compiled. -/
def File.units (f : File) : List (String × String) :=
  f.modules.flatMap fun m =>
    [(m.fileName, m.printUnit), (m.implFileName, m.printImpl)]

/-- Every unit in one text, for a terminal that has nowhere to put files. -/
def File.print (f : File) : String :=
  String.intercalate "\n" (f.units.map (·.2))

end Tatami
