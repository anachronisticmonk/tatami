namespace Tatami

/-- Diagnostics.

    The design note fixes what a generated module looks like; it says nothing
    about which inputs to refuse. Every rejection below is therefore ours, and
    each says plainly what it found. -/
inductive Error where
  | notObjectOrArray (found : String)
  | arrayElementNotObject (index : Nat) (found : String)
  | unsupportedAtThisStage (path : String) (found : String)
  | typeConflict (path : String) (types : String)
  | reservedColumnName (name : String) (column : String)
  | reservedAccessorName (name : String) (generated : String)
  | moduleNameClash (name : String)
  | nestedArray (path : String)
  | mixedElements (path : String)
  | duplicateMember (path : String) (key : String)
  | markingMatchedNothing (path : String)
  | mapEntryNotSupported (path : String) (found : String)
  | illFormedSignature (wherein : String)
  | unusableKey (path : String) (why : String)

def Error.toString : Error → String
  | .notObjectOrArray found =>
      s!"the top-level value is {found}; expected an object, or an array of objects."
  | .arrayElementNotObject i found =>
      s!"element {i} of the top-level array is {found}; every element must be an object."
  | .unsupportedAtThisStage path found =>
      s!"the member at {path} is {found}. Only objects are handled so far; arrays come next."
  | .typeConflict path types =>
      s!"the member {path} holds values of more than one type -- {types} -- and there is none that admits them all."
  | .reservedColumnName name column =>
      s!"the member {name} collides with the generated {column} column."
  | .reservedAccessorName name generated =>
      s!"the member {name} needs an accessor of that name, which collides with the generated {generated}."
  | .moduleNameClash name =>
      s!"two tables would both be called {name}."
  | .nestedArray path =>
      s!"the array at {path} has an element that is itself an array. Wrap the inner array in an object to give it a name."
  | .mixedElements path =>
      s!"the array at {path} has both objects and scalars among its elements."
  | .duplicateMember path key =>
      s!"the object at {path} carries the member {key} more than once."
  | .markingMatchedNothing path =>
      s!"the configuration marks {path} as a map, but no object was found there."
  | .mapEntryNotSupported path found =>
      s!"the member at {path} is {found}. Map entries may be objects or scalars."
  | .unusableKey path why =>
      s!"the member id at {path} cannot be the table's key: it is {why}. Rename it, or remove it and one will be generated."
  | .illFormedSignature wherein =>
      s!"the signature generated for {wherein} repeats a field, value or module name, so it would not compile. This is a bug in tatami; please report the input that produced it."

instance : ToString Error := ⟨Error.toString⟩

end Tatami
