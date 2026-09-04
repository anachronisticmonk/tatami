namespace Tatami

/-- Diagnostics.

    The design note fixes what a generated module looks like; it says nothing
    about which inputs to refuse. Every rejection below is therefore ours, and
    each says plainly what it found. -/
inductive Error where
  | notObjectOrArray (found : String)
  | arrayElementNotObject (index : Nat) (found : String)
  | unsupportedAtThisStage (path : String) (found : String)
  | typeConflict (path : String) (left right : String)
  | reservedColumnName (name : String) (column : String)
  | reservedAccessorName (name : String)
  | moduleNameClash (name : String)
  | nestedArray (path : String)
  | mixedElements (path : String)
  | duplicateMember (path : String) (key : String)

def Error.toString : Error → String
  | .notObjectOrArray found =>
      s!"the top-level value is {found}; expected an object, or an array of objects."
  | .arrayElementNotObject i found =>
      s!"element {i} of the top-level array is {found}; every element must be an object."
  | .unsupportedAtThisStage path found =>
      s!"the member at {path} is {found}. Only objects are handled so far; arrays come next."
  | .typeConflict path left right =>
      s!"the member {path} holds both {left} and {right}, which have no common type."
  | .reservedColumnName name column =>
      s!"the member {name} collides with the generated {column} column."
  | .reservedAccessorName name =>
      s!"the member {name} holds an object, so it needs an accessor of that name, which collides with the generated get."
  | .moduleNameClash name =>
      s!"two tables would both be called {name}."
  | .nestedArray path =>
      s!"the array at {path} has an element that is itself an array. Wrap the inner array in an object to give it a name."
  | .mixedElements path =>
      s!"the array at {path} has both objects and scalars among its elements."
  | .duplicateMember path key =>
      s!"the object at {path} carries the member {key} more than once."

instance : ToString Error := ⟨Error.toString⟩

end Tatami
