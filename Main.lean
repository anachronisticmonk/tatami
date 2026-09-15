import Tatami
import Lean.Data.Json

open Lean Tatami

structure Outcome where
  /-- what the tables are called, which the report needs too -/
  naming : Naming
  /-- every unit as (file name, contents), in compile order -/
  units : List (String × String)
  /-- the same units in one text, for a terminal -/
  ocaml : String
  tables : Tables
  documents : Nat

/-- Everything downstream of inference: the schema, the modules, the report. -/
def finish (cfg : Config) (tables : Tables) (documents : Nat) : Except String Outcome :=
  match
    (do
      let tables ← inferFinish cfg tables
      let nm : Naming := { root := rootModuleName cfg.root, tables := cfg.names }
      let schema := toSchema tables
      let file ← gen nm schema
      return { naming := nm
             , units := file.units
             , ocaml := file.print
             , tables := tables, documents := documents }
      : Except Error Outcome)
  with
  | .error e => .error e.toString
  | .ok o => .ok o

/-- Read a file without holding it: documents are folded in one at a time, so
    memory is a chunk plus one document plus the accumulator rather than some
    forty-five times the corpus. -/
def pipelineFile (cfg : Config) (path : String) : IO (Except String Outcome) := do
  let size := (← (System.FilePath.mk path).metadata).byteSize.toNat
  let h ← IO.FS.Handle.mk path .read
  let step (acc : Tables × Nat) (d : Doc) : IO (Except String (Tables × Nat)) :=
    return match inferStep cfg acc.1 d with
      | .error e => .error e.toString
      | .ok ts => .ok (ts, acc.2 + 1)
  match ← Stream.foldDocuments h size (1 <<< 20) ([], 0) step with
  | .error e => return .error e
  | .ok (tables, n) => return finish cfg tables n

/-- JSON text to OCaml module signatures, plus what was observed on the way. -/
def pipeline (cfg : Config) (input : String) : Except String Outcome :=
  match Doc.parse input with
  | .error e => .error s!"parse error: {e}"
  | .ok j =>
      match
        (do
          let docs ← documents j
          let mut ts : Tables := []
          for d in docs do
            ts ← inferStep cfg ts d
          return (ts, docs.length)
          : Except Error (Tables × Nat))
      with
      | .error e => .error e.toString
      | .ok (ts, n) => finish cfg ts n

private def nat (n : Nat) : Json := .num ⟨(n : Int), 0⟩

def columnJson (nm : Naming) (kv : String × Obs) : Json :=
  let (key, obs) := kv
  Json.mkObj
    [ ("key", .str key)
    , ("name", .str (mangle key))
    , ("type", .str (fieldTyExpr nm obs.field).print)   -- as it appears in the .mli
    , ("values", nat obs.values)
    , ("nulls", nat obs.nulls)
    , ("absent", nat obs.absent)
    , ("widened", .bool obs.widened)
    , ("big", .bool obs.big)
    , ("renamed", .bool (mangle key != key))
    , ("neverTyped", .bool (obs.ty == .bot)) ]

def tableJson (nm : Naming) (pt : Path × TableObs) : Json :=
  let (p, t) := pt
  let sorted := (t.members.toArray.qsort (fun a b => a.1 < b.1)).toList
  Json.mkObj
    [ ("path", .str (Path.toString p))
    , ("module", .str (moduleName nm p))
    , ("visits", nat t.visits)
    , ("columns", .arr (sorted.map (columnJson nm)).toArray) ]

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
        , ("files", .arr (o.units.map (fun u =>
            Json.mkObj [("name", .str u.1), ("ocaml", .str u.2)])).toArray)
        , ("documents", nat o.documents)
        , ("tables", .arr (ordered.map (tableJson o.naming)).toArray) ]

/-- `tatami [--json] [--config FILE] [-o DIR] [INPUT]`

    One `.mli` per module. With `-o` they are written there; without it they
    all go to stdout, each behind its own `(* name *)` banner. -/
def main (args : List String) : IO UInt32 := do
  let jsonMode := args.contains "--json"
  let rest := args.filter (fun a => a != "--json")
  let rec split : List String → Option String × Option String × List String
    | "--config" :: f :: tl => let (_, o, r) := split tl; (some f, o, r)
    | "-o" :: d :: tl => let (c, _, r) := split tl; (c, some d, r)
    | a :: tl => let (c, o, r) := split tl; (c, o, a :: r)
    | [] => (none, none, [])
  let (configFile, outDir, files) := split rest
  let configText ← match configFile with
    | some f => IO.FS.readFile f
    | none => pure ""
  let result ←
    match Config.parse configText with
    | .error e => pure (.error s!"configuration error: {e}")
    | .ok cfg =>
        match files with
        | [] => do
            -- standard input is read whole: it has no size to bound a loop
            -- with, and nothing sends a corpus down a pipe
            let input ← (← IO.getStdin).readToEnd
            pure (pipeline cfg input)
        | p :: _ => pipelineFile cfg p
  if jsonMode then
    IO.println (reportJson result).compress
    return 0
  else
    match result with
    | .ok o =>
        match outDir with
        | none => IO.print o.ocaml
        | some dir =>
            IO.FS.createDirAll dir
            for (name, text) in o.units do
              IO.FS.writeFile (dir ++ "/" ++ name) text
            IO.println s!"wrote {o.units.length} files to {dir}/"
        return 0
    | .error msg => (← IO.getStderr).putStrLn msg; return 1
