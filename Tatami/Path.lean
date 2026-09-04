namespace Tatami

/-- A step from an object into one of its parts. -/
inductive Seg where
  | member : String → Seg
  | elem                    -- into the elements of an array
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A position in the document, from the root down. The empty path is the
    root object.

    A path identifies a table, so it is also what module names are derived
    from. Distinct tables have distinct paths by construction. -/
abbrev Path := List Seg

def Seg.toString : Seg → String
  | .member k => "." ++ k
  | .elem => "[]"

def Path.toString (p : Path) : String :=
  if p.isEmpty then "." else String.join (p.map Seg.toString)

def Path.member (p : Path) (k : String) : Path := p ++ [.member k]
def Path.elem (p : Path) : Path := p ++ [.elem]

/-- The member names along a path, which is what a module is named after.
    The element marker contributes nothing: an array's element table takes
    its name from the member holding the array. -/
def Path.names (p : Path) : List String :=
  p.filterMap fun s => match s with | .member k => some k | .elem => none

def Path.isElement (p : Path) : Bool := p.getLast? == some Seg.elem

/-- For an element table, the table holding the member whose elements it
    describes: drop the element marker and the member it belongs to. -/
def Path.parentOfElement (p : Path) : Option Path :=
  match p.reverse with
  | Seg.elem :: Seg.member _ :: rest => some rest.reverse
  | _ => none

end Tatami
