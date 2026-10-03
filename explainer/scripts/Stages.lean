import Tatami
import Lean.Data.Json
open Lean Tatami

/-- Every intermediate value the pipeline passes through, for one corpus.
    Printed straight from the real functions -- nothing here is transcribed.

    Two renderings of each value are emitted. The structured one feeds the
    tables and panels on the page; the `*Lean` one is the value written the
    way it would be written in Lean, so the page can show the raw intermediate
    beside the picture of it. Both come off the same value, so they cannot
    disagree.

    The layout in the `*Lean` renderings is chosen so that no line runs past
    about eighty columns: a raw value nobody can read without scrolling
    sideways is not showing them anything. Where a term is broken across
    lines it is the same term, written with more whitespace. -/

private def nat (n : Nat) : Json := .num ⟨(n : Int), 0⟩

/-! ## Rendering a value as Lean source

    Nothing here interprets: each function walks one constructor at a time and
    writes what it sees. -/

private def q (s : String) : String :=
  "\"" ++ ((s.replace "\\" "\\\\").replace "\"" "\\\"") ++ "\""

private def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- The width of the widest quoted key, so a column of records lines up. -/
private def keyWidth (ks : List (String × α)) : Nat :=
  ks.foldl (fun a kv => max a (q kv.1).length) 0

private def key (w : Nat) (k : String) : String :=
  "(" ++ q k ++ "," ++ spaces (w - (q k).length) ++ " "

private def segLean : Seg → String
  | .member k => ".member " ++ q k
  | .elem => ".elem"
  | .entry => ".entry"

private def pathLean (p : Path) : String :=
  "[" ++ String.intercalate ", " (p.map segLean) ++ "]"

private def tyLean : Ty → String
  | .bot => ".bot"
  | .int => ".int"
  | .float => ".float"
  | .uuid => ".uuid"
  | .str => ".str"
  | .bool => ".bool"
  | .ref p => ".ref " ++ pathLean p
  | .coll p => ".coll " ++ pathLean p

/-! ### `List Doc`, as `documents` returns it -/

mutual
private def docLean : Doc → String
  | .null => ".null"
  | .bool b => ".bool " ++ toString b
  | .num s => ".num " ++ q s
  | .str s => ".str " ++ q s
  | .arr xs => ".arr [" ++ docListLean xs ++ "]"
  | .obj ms => ".obj [" ++ docMembersLean ms ++ "]"

private def docListLean : List Doc → String
  | [] => ""
  | [d] => docLean d
  | d :: tl => docLean d ++ ", " ++ docListLean tl

private def docMembersLean : List (String × Doc) → String
  | [] => ""
  | [(k, v)] => "(" ++ q k ++ ", " ++ docLean v ++ ")"
  | (k, v) :: tl => "(" ++ q k ++ ", " ++ docLean v ++ "), " ++ docMembersLean tl
end

/-- A member's value, given the column it starts at: an array long enough to
    run off the page is written one element per line. -/
private def docValLean (ind : Nat) (v : Doc) : String :=
  match v with
  | .arr xs =>
      let flat := docLean v
      if flat.length ≤ 52 then flat
      else ".arr [ "
        ++ String.intercalate ("\n" ++ spaces (ind + 5) ++ ", ") (xs.map docLean)
        ++ " ]"
  | _ => docLean v

/-- A document: one member per line, since this is the value a reader is
    meant to compare against the JSON in the step before. -/
private def docTopLean : Doc → String
  | .obj ms =>
      let w := keyWidth ms
      let items := ms.map fun (k, v) =>
        key w k ++ docValLean (9 + w + 3) v ++ ")"
      ".obj [ " ++ String.intercalate "\n       , " items ++ " ]"
  | d => docLean d

private def docsLean (ds : List Doc) : String :=
  "[ " ++ String.intercalate "\n\n, " (ds.map docTopLean) ++ " ]"

/-! ### `Tables`, as the walk, the merge and `inferFinish` return it -/

/-- `ind` is the column the continuation aligns on, so that a member whose
    `seen` list is long does not push the counts off the page. -/
private def obsLean (ind : Nat) (o : Obs) : String :=
  "{ seen := [" ++ String.intercalate ", " (o.seen.map tyLean) ++ "]"
    ++ "\n" ++ spaces ind
    ++ ", values := " ++ toString o.values
    ++ ", nulls := " ++ toString o.nulls
    ++ ", absent := " ++ toString o.absent
    ++ ", big := " ++ toString o.big ++ " }"

private def tableObsLean (t : TableObs) : String :=
  let w := keyWidth t.members
  let items := t.members.map fun (k, o) => key w k ++ obsLean (8 + w + 3) o ++ ")"
  "{ visits := " ++ toString t.visits
    ++ ", elemObject := " ++ toString t.elemObject
    ++ ", elemScalar := " ++ toString t.elemScalar
    ++ "\n    , members :=\n      [ " ++ String.intercalate "\n      , " items ++ " ] }"

private def tablesLean (ts : Tables) : String :=
  if ts.isEmpty then "[]" else
  "[ " ++ String.intercalate "\n\n, "
    (ts.map fun (p, t) => "( " ++ pathLean p ++ "\n  , " ++ tableObsLean t ++ " )") ++ " ]"

/-! ### `Naming`, `Schema` -/

private def namingLean (nm : Naming) : String :=
  "{ root := " ++ q nm.root
    ++ "\n, tables := ["
    ++ String.intercalate ", "
        (nm.tables.map fun (p, n) => "(" ++ pathLean p ++ ", " ++ q n ++ ")")
    ++ "] }"

private def tableLean (t : Table) : String :=
  -- the field goes on its own line: a `coll` type carries a whole path, and
  -- beside a name it runs off the page
  let cols := t.columns.map fun c =>
    "{ name := " ++ q c.name
      ++ "\n" ++ spaces 8 ++ ", field := { ty := " ++ tyLean c.field.ty
      ++ ", nullable := " ++ toString c.field.nullable ++ " } }"
  "{ path := " ++ pathLean t.path
    ++ "\n  , parent := " ++ (match t.parent with
        | some p => "some " ++ pathLean p
        | none => "none")
    ++ "\n  , keyed := " ++ toString t.keyed
    ++ "\n  , columns :=\n      [ " ++ String.intercalate "\n      , " cols ++ " ] }"

private def schemaLean (s : Schema) : String :=
  if s.isEmpty then "[]" else
  "[ " ++ String.intercalate "\n\n, " (s.map tableLean) ++ " ]"

/-! ### `File`: modules and the declarations of their `.mli`s -/

private def tyExprLean : TyExpr → String
  | .id => ".id"
  | .int => ".int"
  | .float => ".float"
  | .string => ".string"
  | .bool => ".bool"
  | .unit => ".unit"
  | .option t => ".option (" ++ tyExprLean t ++ ")"
  | .list t => ".list (" ++ tyExprLean t ++ ")"
  | .named n => ".named " ++ q n
  | .qualified m n => ".qualified " ++ q m ++ " " ++ q n
  | .arrow a b => ".arrow (" ++ tyExprLean a ++ ") (" ++ tyExprLean b ++ ")"
  | .labelled l a b =>
      ".labelled " ++ q l ++ " (" ++ tyExprLean a ++ ") (" ++ tyExprLean b ++ ")"

/-- `arrow` and `labelled` nest to the right, so a `val`'s type is a spine.
    Written flat while it fits and one argument per line once it does not --
    the same term either way, and the closing parens pile up at the end
    exactly as they do in source. -/
private def tySpineLean (ind : Nat) : TyExpr → String
  | .arrow a b =>
      let flat := tyExprLean (.arrow a b)
      if flat.length ≤ 60 then "(" ++ flat ++ ")"
      else "(.arrow (" ++ tyExprLean a ++ ")\n" ++ spaces ind ++ tySpineLean ind b ++ ")"
  | .labelled l a b =>
      let flat := tyExprLean (.labelled l a b)
      if flat.length ≤ 60 then "(" ++ flat ++ ")"
      else "(.labelled " ++ q l ++ " (" ++ tyExprLean a ++ ")\n"
             ++ spaces ind ++ tySpineLean ind b ++ ")"
  | t => "(" ++ tyExprLean t ++ ")"

/-- Only the four constructors an `.mli` can hold are written out. A `.ml`
    body is an `Expr`, and well-formedness is stated of `decls` alone, so the
    implementation is counted rather than printed. -/
private def declLean (ind : Nat) : Decl → String
  | .abstractType n => ".abstractType " ++ q n
  | .typeAlias n t => ".typeAlias " ++ q n ++ " (" ++ tyExprLean t ++ ")"
  | .recordType n fs =>
      ".recordType " ++ q n ++ " ["
        ++ String.intercalate ", "
            (fs.map fun f => "⟨" ++ q f.name ++ ", " ++ tyExprLean f.ty ++ "⟩")
        ++ "]"
  | .value n t =>
      let flat := tyExprLean t
      if flat.length ≤ 60 then ".value " ++ q n ++ " (" ++ flat ++ ")"
      else ".value " ++ q n ++ "\n" ++ spaces (ind + 4) ++ tySpineLean (ind + 4) t
  | .letValue n as _ =>
      ".letValue " ++ q n ++ " [" ++ String.intercalate ", " (as.map q) ++ "] …"

private def moduleLean (m : Tatami.Module) : String :=
  "{ name := " ++ q m.name ++ ", implOnly := " ++ toString m.implOnly
    ++ (if m.decls.isEmpty then "\n    , decls := []"
        else "\n    , decls :=\n      [ "
               ++ String.intercalate "\n      , " (m.decls.map (declLean 8)) ++ " ]")
    ++ "\n    , impl := … " ++ toString m.impl.length ++ " declarations }"

private def fileLean (f : File) : String :=
  "{ modules :=\n  [ "
    ++ String.intercalate "\n\n  , " (f.modules.map moduleLean) ++ " ] }"

/-- The record `finish` builds and `pipeline` returns. Its five field names are
    declared in `Main.lean`, which a script cannot import -- `Main` already
    declares a `main`. Every value below is the real one; `units` and `ocaml`
    are the same text step 9 shows in full, so they are given by size. -/
private def outcomeLean (nm : Naming) (f : File) (ts : Tables) (n : Nat) : String :=
  let us := f.units
  "{ naming    := " ++ ((namingLean nm).replace "\n" "\n               ")
    ++ "\n, units     := [ "
    ++ String.intercalate "\n               , "
        (us.map fun u => "(" ++ q u.1 ++ ", … " ++ toString u.2.length ++ " chars)")
    ++ " ]"
    ++ "\n, ocaml     := … " ++ toString f.print.length ++ " chars, every unit in one text"
    ++ "\n, tables    := … " ++ toString ts.length ++ " tables, the value of step 5"
    ++ "\n, documents := " ++ toString n ++ " }"

/-! ## The structured rendering the page's tables read -/

def obsJson (ko : String × Obs) : Json :=
  let (k, o) := ko
  Json.mkObj
    [ ("key", .str k)
    , ("seen", .arr (o.seen.map (fun t => Json.str t.toString)).toArray)
    , ("joined", .str (match o.joined with | some t => t.toString | none => "—"))
    , ("values", nat o.values), ("nulls", nat o.nulls), ("absent", nat o.absent) ]

def tableObsJson (pt : Path × TableObs) : Json :=
  let (p, t) := pt
  Json.mkObj
    [ ("path", .str (Path.toString p))
    , ("visits", nat t.visits)
    , ("elemObject", .bool t.elemObject)
    , ("members", .arr (t.members.map obsJson).toArray) ]

def tablesJson (ts : Tables) : Json := .arr (ts.map tableObsJson).toArray

def schemaJson (s : Schema) : Json :=
  .arr (s.map (fun t => Json.mkObj
    [ ("path", .str (Path.toString t.path))
    , ("parent", match t.parent with | some p => .str (Path.toString p) | none => .null)
    , ("keyed", .bool t.keyed)
    , ("columns", .arr (t.columns.map (fun c => Json.mkObj
        [ ("name", .str c.name)
        , ("ty", .str c.field.ty.toString)
        , ("nullable", .bool c.field.nullable) ])).toArray) ])).toArray

def fileJson (f : File) : Json :=
  .arr (f.modules.map (fun m => Json.mkObj
    [ ("name", .str m.name)
    , ("implOnly", .bool m.implOnly)
    , ("decls", .arr (m.decls.map (fun d => Json.str d.print)).toArray) ])).toArray

def run (src : String) : Json :=
  match Doc.parse src with
  | .error e => Json.mkObj [("error", .str e)]
  | .ok j =>
    match documents j with
    | .error e => Json.mkObj [("error", .str e.toString)]
    | .ok ds =>
      let cfg : Config := {}
      let per := ds.map (fun d => (observeDocument cfg d).toOption.getD [])
      let folded := per.foldl Tables.merge []
      match inferFinish cfg folded with
      | .error e => Json.mkObj [("error", .str e.toString)]
      | .ok fin =>
        let sch := toSchema fin
        let nm : Naming := { root := rootModuleName cfg.root, tables := cfg.names }
        Json.mkObj
          [ ("documents", nat ds.length)
          , ("docs", .str (docsLean ds))
          , ("perDocument", .arr (per.map tablesJson).toArray)
          , ("perDocumentLean", .arr (per.map (fun t => Json.str (tablesLean t))).toArray)
          , ("folded", tablesJson folded)
          , ("foldedLean", .str (tablesLean folded))
          , ("finished", tablesJson fin)
          , ("finishedLean", .str (tablesLean fin))
          , ("naming", .str (namingLean nm))
          , ("schema", schemaJson sch)
          , ("schemaLean", .str (schemaLean sch))
          , ("file", match gen nm sch with
              | .ok f => fileJson f
              | .error e => Json.str e.toString)
          , ("fileLean", match gen nm sch with
              | .ok f => Json.str (fileLean f)
              | .error e => Json.str e.toString)
          , ("outcome", match gen nm sch with
              | .ok f => Json.str (outcomeLean nm f fin ds.length)
              | .error e => Json.str e.toString)
          , ("units", match gen nm sch with
              | .ok f => .arr (f.units.map (fun u => Json.mkObj
                  [("name", .str u.1), ("text", .str u.2)])).toArray
              | .error _ => .arr #[]) ]

def main (args : List String) : IO Unit := do
  let src ← IO.FS.readFile (args.headD "explainer/scripts/corpus.json")
  IO.println (run src).compress
