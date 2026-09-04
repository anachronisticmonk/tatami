import Tatami.Path
import Tatami.Ty

namespace Tatami

structure Column where
  /-- the JSON member name, unmangled -/
  name : String
  field : Field
  deriving Repr

structure Table where
  /-- the path this table came from; it is the table's identity and the
      source of its module name -/
  path : Path
  /-- set when rows sit in a collection: the table they point back to -/
  parent : Option Path
  /-- the table is also reached other than through that collection, so the
      back-reference and position are not always present -/
  parentOptional : Bool
  /-- rows are keyed by a string rather than positioned by an index -/
  keyed : Bool
  columns : List Column
  deriving Repr

abbrev Schema := List Table

end Tatami
