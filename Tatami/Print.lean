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

def Decl.print : Decl → String
  | .abstractType n => s!"type {n}"
  | .recordType n fields =>
      let body := String.intercalate "; "
        (fields.map fun f => s!"{f.name} : {f.ty.print}")
      s!"type {n} = \{ {body} }"
  | .value n ty => s!"val {n} : {ty.print}"

def Module.print (keyword : String) (m : Module) : String :=
  let body := String.intercalate "\n" (m.decls.map fun d => "  " ++ d.print)
  s!"{keyword} {m.name} : sig\n{body}\nend"

def File.print (f : File) : String :=
  let header := "(* generated.mli *)\n"
  match f.modules with
  | [] => header
  | first :: rest =>
      let firstKeyword := if f.recursive then "module rec" else "module"
      let restKeyword := if f.recursive then "and" else "module"
      let body := String.intercalate "\n\n"
        (Module.print firstKeyword first :: rest.map (Module.print restKeyword))
      header ++ "\n" ++ body ++ "\n"

end Tatami
