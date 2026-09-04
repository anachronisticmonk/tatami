namespace Tatami

/-- A step from an object into one of its parts. -/
inductive Seg where
  | member : String → Seg
  | elem                    -- into the elements of an array
  | entry                   -- into the entries of an object marked as a map
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A position in the document, from the root down. The empty path is the
    root object.

    A path identifies a table, so it is also what module names are derived
    from. Distinct tables have distinct paths by construction. -/
abbrev Path := List Seg

def Seg.toString : Seg → String
  | .member k => "." ++ k
  | .elem => "[]"
  | .entry => "{}"

def Path.toString (p : Path) : String :=
  if p.isEmpty then "." else String.join (p.map Seg.toString)

def Path.member (p : Path) (k : String) : Path := p ++ [.member k]
def Path.elem (p : Path) : Path := p ++ [.elem]
def Path.entry (p : Path) : Path := p ++ [.entry]

/-- The member names along a path, which is what a module is named after.
    The element marker contributes nothing: an array's element table takes
    its name from the member holding the array. -/
def Path.names (p : Path) : List String :=
  p.filterMap fun s => match s with | .member k => some k | _ => none

def Path.isElement (p : Path) : Bool := p.getLast? == some Seg.elem
def Path.isEntry (p : Path) : Bool := p.getLast? == some Seg.entry

/-- Rows of this table sit in a collection, so they carry a key back to the
    table that holds them. -/
def Path.inCollection (p : Path) : Bool := p.isElement || p.isEntry

/-- For an element table, the table holding the member whose elements it
    describes: drop the element marker and the member it belongs to. -/
def Path.parentOfElement (p : Path) : Option Path :=
  match p.reverse with
  | Seg.elem :: Seg.member _ :: rest => some rest.reverse
  | Seg.entry :: Seg.member _ :: rest => some rest.reverse
  | _ => none

/-- Read a path back from the form it is written in, as `.a.b[]` or `.u{}`.
    A lone `.` is the root.

    `partial` for the same reason as the document reader: the input shrinks at
    every step, but showing that to Lean would mean carrying the proof through
    the return type. -/
private partial def parseGo (acc : Path) : List Char → Except String Path
  | [] => .ok acc.reverse
  | '[' :: ']' :: rest => parseGo (Seg.elem :: acc) rest
  | '{' :: '}' :: rest => parseGo (Seg.entry :: acc) rest
  | '.' :: rest =>
      let name := rest.takeWhile fun c => c != '.' && c != '[' && c != '{'
      if name.isEmpty then .error "a path segment needs a member name after '.'"
      else parseGo (Seg.member (String.ofList name) :: acc) (rest.drop name.length)
  | c :: _ => .error s!"unexpected '{c}' in path"

def Path.parse (s : String) : Except String Path :=
  if s.isEmpty then .error "empty path"
  else if s == "." then .ok []
  else if s.front != '.' then .error s!"a path must begin with '.': {s}"
  else parseGo [] s.toList

end Tatami
