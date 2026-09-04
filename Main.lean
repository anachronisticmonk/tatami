import Tatami
import Lean.Data.Json

open Lean Tatami

structure Outcome where
  ocaml : String
  tables : Tables
  documents : Nat

/-- JSON text to OCaml module signatures, plus what was observed on the way. -/
def pipeline (input : String) : Except String Outcome :=
  match Doc.parse input with
  | .error e => .error s!"parse error: {e}"
  | .ok j =>
      match
        (do
          let docs ← documents j
          let tables ← inferCorpus docs
          let file ← gen (toSchema tables)
          return { ocaml := file.print, tables := tables, documents := docs.length }
          : Except Error Outcome)
      with
      | .error e => .error e.toString
      | .ok o => .ok o

private def nat (n : Nat) : Json := .num ⟨(n : Int), 0⟩

def columnJson (kv : String × Obs) : Json :=
  let (key, obs) := kv
  Json.mkObj
    [ ("key", .str key)
    , ("name", .str (mangle key))
    , ("type", .str (fieldTyExpr obs.field).print)   -- as it appears in the .mli
    , ("values", nat obs.values)
    , ("nulls", nat obs.nulls)
    , ("absent", nat obs.absent)
    , ("widened", .bool obs.widened)
    , ("big", .bool obs.big)
    , ("renamed", .bool (mangle key != key))
    , ("neverTyped", .bool (obs.ty == .bot)) ]

def tableJson (pt : Path × TableObs) : Json :=
  let (p, t) := pt
  let sorted := (t.members.toArray.qsort (fun a b => a.1 < b.1)).toList
  Json.mkObj
    [ ("path", .str (Path.toString p))
    , ("module", .str (moduleName p))
    , ("visits", nat t.visits)
    , ("columns", .arr (sorted.map columnJson).toArray) ]

def reportJson : Except String Outcome → Json
  | .error msg => Json.mkObj [("ok", .bool false), ("error", .str msg)]
  | .ok o =>
      -- deepest first, matching the order the modules are emitted in
      let ordered := (o.tables.toArray.qsort fun a b =>
        if a.1.length == b.1.length then Path.toString a.1 < Path.toString b.1
        else a.1.length > b.1.length).toList
      Json.mkObj
        [ ("ok", .bool true)
        , ("ocaml", .str o.ocaml)
        , ("documents", nat o.documents)
        , ("tables", .arr (ordered.map tableJson).toArray) ]

def main (args : List String) : IO UInt32 := do
  let jsonMode := args.contains "--json"
  let files := args.filter (fun a => a != "--json")
  let input ← match files with
    | [] => (← IO.getStdin).readToEnd
    | p :: _ => IO.FS.readFile p
  let result := pipeline input
  if jsonMode then
    IO.println (reportJson result).compress
    return 0
  else
    match result with
    | .ok o => IO.print o.ocaml; return 0
    | .error msg => (← IO.getStderr).putStrLn msg; return 1
