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
  /-- set for an element table: the table its rows point back to -/
  parent : Option Path
  columns : List Column
  deriving Repr

abbrev Schema := List Table

end Tatami
