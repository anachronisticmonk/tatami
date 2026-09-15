import Tatami.Doc
import Tatami.Path

namespace Tatami

/-- Markings the user supplies alongside a corpus.

    One shape cannot be read off the data: an object whose keys are values
    rather than field names looks exactly like a record. Guessing from the
    data would make the schema a function of the sample rather than of the
    shape, so it is marked instead.

    There was a second marking, `recursive`, folding a path into an ancestor
    so both became one table. It is gone. A table is now identified by its
    path and nothing else, which is what makes its parent and its position
    column functions of that path rather than of the documents. The cost is
    recorded under known gaps: a self-referential shape yields one table per
    level the sample happened to reach. -/
structure Config where
  /-- objects whose members are data: each becomes a row keyed by its name -/
  maps : List Path := []
  /-- what to call the root table. Every other table is named for the members
      along its path; the root path has none, so its name is invented and
      `Root` is only a fallback. This is where a better one comes from. -/
  root : Option String := none
  /-- what to call any other table, by the path of the table it names. The
      root's name was always supplied for want of a path to derive one from;
      these are supplied because a derived name says where a table came from
      rather than what it is, and `.runs[].jobs[]` is a worse name for a job
      than `job` is. -/
  names : List (Path × String) := []
  deriving Inhabited

def Config.empty : Config := {}

def Config.isMap (c : Config) (p : Path) : Bool := c.maps.contains p

/-- Read the markings from JSON:

    { "maps": [".users"], "root": "repo", "names": { ".runs[]": "run" } } -/
def Config.ofDoc : Doc → Except String Config
  | .obj members => do
      let mut cfg : Config := {}
      for (k, v) in members do
        if k == "maps" then
          match v with
          | .arr xs =>
              let mut ps : List Path := []
              for x in xs do
                match x with
                | .str s => ps := ps ++ [← Path.parse s]
                | _ => throw "maps must be a list of path strings"
              cfg := { cfg with maps := ps }
          | _ => throw "maps must be a list"
        else if k == "root" then
          match v with
          | .str n =>
              if n.trimAscii.isEmpty then throw "root must not be empty"
              cfg := { cfg with root := some n }
          | _ => throw "root must be a string"
        else if k == "names" then
          match v with
          | .obj entries =>
              let mut ns : List (Path × String) := []
              for (pk, pv) in entries do
                match pv with
                | .str n =>
                    if n.trimAscii.isEmpty then throw s!"the name for {pk} must not be empty"
                    ns := ns ++ [(← Path.parse pk, n)]
                | _ => throw s!"the name for {pk} must be a string"
              cfg := { cfg with names := ns }
          | _ => throw "names must be an object mapping a path to a name"
        else if k == "recursive" then
          throw "recursive markings are no longer supported: a table is identified by its path, so nothing folds into an ancestor"
        else throw s!"unknown configuration key {k}"
      return cfg
  | _ => .error "the configuration must be an object"

def Config.parse (text : String) : Except String Config := do
  if text.trimAscii.isEmpty then return {}
  Config.ofDoc (← Doc.parse text)

end Tatami
