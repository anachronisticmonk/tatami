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
  /-- set when rows sit in a collection: the table they point back to.
      Derived from `path`, not observed: a table's rows sit in exactly one
      collection, the one its path ends in. -/
  parent : Option Path
  /-- rows are keyed by a string rather than positioned by an index. Also
      derived from `path` -- true exactly when it ends in a map entry. -/
  keyed : Bool
  columns : List Column
  deriving Repr

abbrev Schema := List Table

end Tatami
