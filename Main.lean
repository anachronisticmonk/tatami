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

/-- The layout as a loader and a DDL need it, which is not what `tables`
    above reports.

    `tables` reports what was *observed*: the document's own members, each
    with the JSON key it came from. That is the wrong list to load from. It
    omits the three columns the generator adds -- the key, the back reference
    and the position -- and it includes the collections, which are not columns
    at all but the edges to the tables holding them.

    This reports what is actually *emitted*, straight from `layoutOf`, so that
    nothing downstream reconstructs the generator's rules and then drifts from
    them. Every column says where its value comes from, which is the only
    question a loader asks of one. -/
def layoutColumnJson (s : Schema) (nm : Naming) (c : Col) : Json :=
  Json.mkObj
    ([ ("name", Json.str c.name)
     , ("type", Json.str (storageTy s c.ty).toString)
     , ("nullable", Json.bool c.nullable)
     , ("kind", Json.str (match c.kind with
         | .key => "key"
         | .parent => "parent"
         | .position => "position"
         | .member _ => "member")) ]
     ++ (match c.kind with
         -- the JSON member this came from, before mangling: the loader reads
         -- the document by this name and writes the column by `name`
         | .member src => [("source", Json.str src)]
         | _ => [])
     ++ (match c.ty with
         | .ref p => [("refers", Json.str (idTypeName nm p))]
         | _ => []))

def layoutTableJson (s : Schema) (nm : Naming) (t : Table) : Json :=
  Json.mkObj
    ([ ("table", Json.str (idTypeName nm t.path))
     , ("module", Json.str (moduleName nm t.path))
     -- where the rows are, as a path into the document
     , ("path", Json.str (Path.toString t.path))
     -- rows keyed by a member name rather than positioned by an index, which
     -- is what the position column holds
     , ("keyed", Json.bool t.keyed)
     , ("columns", Json.arr
         (((layoutOf nm t).toOption.getD []).map (layoutColumnJson s nm)).toArray)
     , ("ddl", Json.str (ddlOf s nm t))
     , ("constraints", Json.arr ((constraintsOf nm t).map Json.str).toArray) ]
     ++ (match t.parent with
         | some pp => [("parent", Json.str (idTypeName nm pp))]
         | none => []))

def reportJson : Except String Outcome → Json
  | .error msg => Json.mkObj [("ok", .bool false), ("error", .str msg)]
  | .ok o =>
      -- deepest first, matching the order the modules are emitted in
      let ordered := (o.tables.toArray.qsort fun a b =>
        if a.1.length == b.1.length then Path.toString a.1 < Path.toString b.1
        else a.1.length > b.1.length).toList
      -- `orderTables` is a topological sort of the same graph the foreign keys
      -- run along, so a table always follows the tables it points into. That
      -- makes it the load order too, by construction rather than by care.
      let schema := orderTables (toSchema o.tables)
      Json.mkObj
        [ ("ok", .bool true)
        , ("ocaml", .str o.ocaml)
        , ("files", .arr (o.units.map (fun u =>
            Json.mkObj [("name", .str u.1), ("ocaml", .str u.2)])).toArray)
        , ("documents", nat o.documents)
        , ("tables", .arr (ordered.map (tableJson o.naming)).toArray)
        , ("layout", .arr (schema.map (layoutTableJson schema o.naming)).toArray) ]

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
