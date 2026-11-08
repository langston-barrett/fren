module

public import Std
public import Lean.Data.Name

public section

namespace Fren.Sexp

/-- The format's ASCII atom alphabet. -/
@[expose] def isAtomChar (c : Char) : Bool :=
  c.isAlpha && c.toNat < 128 || c.isDigit ||
    c == '_' || c == '-' || c == '.' || c == ':' || c == '@' ||
    c == '/' || c == '+'

@[expose] def isAtom (s : String) : Bool := !s.isEmpty && s.all isAtomChar

/-- An atom is nonempty and contains only the format's atom characters. -/
abbrev Atom := { s : String // isAtom s = true }

def Atom.ofString? (s : String) : Option Atom :=
  if h : isAtom s = true then some ⟨s, h⟩ else none

instance : Inhabited Atom := ⟨⟨"unit", by native_decide⟩⟩

/-- For codec implementations whose generated symbols are known to be valid.
Invalid symbols are a programming error; text input uses `ofString?`. -/
def Atom.ofString! (s : String) : Atom :=
  match Atom.ofString? s with
  | some a => a
  | none => panic! s!"invalid S-expression atom: {s}"

end Fren.Sexp

namespace Fren

/-- Semantic S-expressions, independent of source locations and layout. -/
inductive Sexp where
  | atom (value : Sexp.Atom)
  | string (value : String)
  | list (items : Array Sexp)
  deriving BEq, Repr, Inhabited

namespace Sexp

/-- Construct a statically known symbol. Invalid input is a programming error. -/
def symbol (s : String) : Sexp := .atom (Atom.ofString! s)

/-- One-based line and Unicode scalar column, plus zero-based UTF-8 byte offset.
Only LF starts a new line; CR is accepted as whitespace. -/
structure Position where
  byteOffset : Nat := 0
  line : Nat := 1
  column : Nat := 1
  deriving BEq, Repr, Inhabited

structure ParseError where
  position : Position
  expected : String
  deriving BEq, Repr, Inhabited

instance : ToString ParseError where
  toString e := s!"{e.position.line}:{e.position.column}: expected {e.expected}"

/-- A semantic decoding error points to a node by its child indices. -/
structure DecodeError where
  path : List Nat := []
  expected : String
  deriving BEq, Repr, Inhabited

/-- Locations are kept separately so semantic AST equality ignores layout. -/
inductive Locations where
  | node (position : Position) (children : Array Locations)
  deriving Inhabited

def Locations.position : Locations → Position
  | .node p _ => p

def Locations.at (loc : Locations) (path : List Nat) : Position :=
  match path, loc with
  | [], .node p _ => p
  | i :: rest, .node p cs =>
    match cs[i]? with
    | some child => child.at rest
    | none => p

structure Located where
  value : Sexp
  locations : Locations
  deriving Inhabited

/-- Convert only the last string component, inserting an underscore before an
ASCII uppercase letter that follows a lowercase letter or a digit. Deriving
must additionally reject collisions between constructors of the same type. -/
def constructorAtom (name : Lean.Name) : Except String Atom := do
  let .str _ last := name | throw "constructor name needs a string component"
  let mut text := ""
  let mut previous : Option Char := none
  for c in last.toList do
    if c.isUpper && previous.any (fun p => p.isLower || p.isDigit) then
      text := text.push '_'
    text := text.push c.toLower
    previous := some c
  if text.isEmpty || text.front.isDigit then
    throw "constructor atom must be nonempty and must not start with a digit"
  match Atom.ofString? text with
  | some a => return a
  | none => throw s!"constructor name does not give an ASCII atom: {last}"

end Sexp
end Fren
