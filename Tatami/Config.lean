import Tatami.Doc
import Tatami.Path

namespace Tatami

/-- Markings the user supplies alongside a corpus.

    Two shapes cannot be read off the data. An object whose keys are values
    rather than field names looks exactly like a record, and a self-referential
    shape looks exactly like a fixed number of nested ones -- how many depends
    on how deep the sample happened to go. Guessing either from the data would
    make the schema a function of the sample rather than of the shape, so both
    are marked instead. -/
structure Config where
  /-- objects whose members are data: each becomes a row keyed by its name -/
  maps : List Path := []
  /-- a path and the ancestor it folds into, so both become one table -/
  recursive : List (Path × Path) := []
  deriving Inhabited

def Config.empty : Config := {}

/-- The table a path belongs to, after folding. Applied once: a fold target
    that itself folds is not followed. -/
def Config.resolve (c : Config) (p : Path) : Path :=
  match c.recursive.find? (fun r => r.1 == p) with
  | some (_, target) => target
  | none => p

def Config.isMap (c : Config) (p : Path) : Bool := c.maps.contains p

/-- Read the markings from JSON:

    { "maps": [".users"],
      "recursive": [ { "path": ".replies[]", "folds_into": "." } ] } -/
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
        else if k == "recursive" then
          match v with
          | .arr xs =>
              let mut rs : List (Path × Path) := []
              for x in xs do
                match x with
                | .obj fs =>
                    match fs.lookup "path", fs.lookup "folds_into" with
                    | some (.str a), some (.str b) =>
                        let pa ← Path.parse a
                        let pb ← Path.parse b
                        if !pb.isPrefixOf pa then
                          throw s!"{b} is not an ancestor of {a}"
                        if pa == pb then
                          throw s!"{a} cannot fold into itself"
                        rs := rs ++ [(pa, pb)]
                    | _, _ => throw "each recursive entry needs path and folds_into"
                | _ => throw "recursive must be a list of objects"
              cfg := { cfg with recursive := rs }
          | _ => throw "recursive must be a list"
        else throw s!"unknown configuration key {k}"
      return cfg
  | _ => .error "the configuration must be an object"

def Config.parse (text : String) : Except String Config := do
  if text.trimAscii.isEmpty then return {}
  Config.ofDoc (← Doc.parse text)

end Tatami
