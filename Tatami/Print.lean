import Tatami.Ocaml

namespace Tatami

/-- The one trusted step: output language to text. Structurally recursive and
    total, so it can be checked by reading. -/

def TyExpr.needsParens : TyExpr → Bool
  | .arrow _ _ => true
  | _ => false

/-- A string, as OCaml spells a literal.

    The accessors never needed this: the only strings they emitted were module
    and column names, which mangling has already restricted to letters, digits
    and underscores. The loader emits two kinds that are not restricted at all
    -- the DDL, which quotes every identifier, and the JSON member name a
    column is read by, which is whatever the document called it. Either can
    contain a quote or a backslash, and an unescaped one ends the literal
    early and turns the rest of the statement into code. -/
def escapeString (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++
      (if c == '"' then "\\\""
       else if c == '\\' then "\\\\"
       else if c == '\n' then "\\n"
       else if c == '\t' then "\\t"
       else if c == '\r' then "\\r"
       else c.toString)) ""

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
  | .str s => "\"" ++ escapeString s ++ "\""
  | .int n => toString n
  | .app f args => String.intercalate " " (Expr.atom f :: Expr.atoms args)
  | .labelledApp f args => String.intercalate " " (Expr.atom f :: Expr.labelledArgs args)
  | .list es => "[" ++ String.intercalate "; " (Expr.prints es) ++ "]"
  -- each binding on its own line: the body of a loader is a sequence of
  -- steps, and a reader checks it by reading down the column
  | .letIn n e body => "let " ++ n ++ " = " ++ Expr.print e ++ " in\n  " ++ Expr.print body
  | .matchStr e cases dflt =>
      "match " ++ Expr.atom e ++ " with\n" ++ String.join (Expr.cases cases)
        ++ "  | _ -> " ++ Expr.print dflt
  | .record fs => "{ " ++ String.intercalate "; " fs ++ " }"
  | .update e f v => "{ " ++ Expr.atom e ++ " with " ++ f ++ " = " ++ Expr.atom v ++ " }"

def Expr.atom : Expr → String
  | .app f args => "(" ++ String.intercalate " " (Expr.atom f :: Expr.atoms args) ++ ")"
  | .labelledApp f args =>
      "(" ++ String.intercalate " " (Expr.atom f :: Expr.labelledArgs args) ++ ")"
  | .letIn n e body =>
      "(let " ++ n ++ " = " ++ Expr.print e ++ " in\n  " ++ Expr.print body ++ ")"
  -- already delimited, so an argument position needs nothing added
  | .list es => "[" ++ String.intercalate "; " (Expr.prints es) ++ "]"
  -- `f -1` is `f` minus one, not `f` applied to minus one
  | .int n => if n < 0 then "(" ++ toString n ++ ")" else toString n
  | .matchStr e cases dflt =>
      "(match " ++ Expr.atom e ++ " with\n" ++ String.join (Expr.cases cases)
        ++ "  | _ -> " ++ Expr.print dflt ++ ")"
  | .var n => n
  | .field e f => Expr.atom e ++ "." ++ f
  | .qual m n => m ++ "." ++ n
  | .str s => "\"" ++ escapeString s ++ "\""
  | .record fs => "{ " ++ String.intercalate "; " fs ++ " }"
  | .update e f v => "{ " ++ Expr.atom e ++ " with " ++ f ++ " = " ++ Expr.atom v ++ " }"

def Expr.atoms : List Expr → List String
  | [] => []
  | e :: tl => Expr.atom e :: Expr.atoms tl

/-- List elements are separated by `;`, which binds looser than application,
    so an element needs no parentheses of its own. -/
def Expr.prints : List Expr → List String
  | [] => []
  | e :: tl => Expr.print e :: Expr.prints tl

def Expr.labelledArgs : List (String × Expr) → List String
  | [] => []
  | (n, e) :: tl => ("~" ++ n ++ ":" ++ Expr.atom e) :: Expr.labelledArgs tl

def Expr.cases : List (String × Expr) → List String
  | [] => []
  | (k, e) :: tl => ("  | \"" ++ k ++ "\" -> " ++ Expr.print e ++ "\n") :: Expr.cases tl

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
      -- a body that binds starts on the next line, so the bindings line up
      match body with
      | .letIn _ _ _ => s!"let {n}{ps} =\n  {body.print}"
      | .matchStr _ _ _ => s!"let {n}{ps} =\n  {body.print}"
      | _ => s!"let {n}{ps} = {body.print}"

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
    if m.implOnly then [(m.implFileName, m.printImpl)]
    else [(m.fileName, m.printUnit), (m.implFileName, m.printImpl)]

/-- Every unit in one text, for a terminal that has nowhere to put files. -/
def File.print (f : File) : String :=
  String.intercalate "\n" (f.units.map (·.2))

end Tatami
