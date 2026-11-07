module

public import FrenSexp.Codec

namespace Fren.Sexp

/-!
Name strings use Lean's `«component»` notation, with dots between components.
Bare decimal components denote `Name.num`; quoted ones always denote `Name.str`.
The empty name string denotes `Name.anonymous`, while `«»` is an empty string
component. This avoids the ambiguities of `Name.toString`, whose documentation
explicitly excludes numeric, anonymous and `»`-containing names from round trips.

The issue does not specify these distinctions. For arbitrary internal names we
extend Lean's notation *inside quoted components*: `\\` denotes a backslash
and `\»` denotes a closing guillemet. These are name-level escapes; the outer
S-expression string still uses exactly the four specified string escapes.
-/

private def bareComponent (s : String) : Bool :=
  isAtom s && !s.contains '.' && !s.all Char.isDigit

private def quotedComponent (s : String) : String := Id.run do
  let mut out := "«"
  for c in s.toList do
    if c == '\\' || c == '»' then out := out.push '\\'
    out := out.push c
  return out ++ "»"

private def nameParts : Lean.Name → List String
  | .anonymous => []
  | .str parent part => nameParts parent ++
      [if bareComponent part then part else quotedComponent part]
  | .num parent n => nameParts parent ++ [toString n]

private def bareName : Lean.Name → Bool
  | .anonymous => false
  | .str .anonymous s => bareComponent s
  | .str parent s => bareName parent && bareComponent s
  | .num _ _ => false

@[no_expose] public instance : Fren.ToSexp Lean.Name where
  toSexp name :=
    let text := ".".intercalate (nameParts name)
    if bareName name then .symbol text else .string text

private def readQuoted (chars : List Char) : Except DecodeError (String × List Char) := do
  let mut chars := chars
  let mut out := ""
  repeat
    match chars with
    | [] => return ← expected "a closing » in a name component"
    | '»' :: rest => return (out, rest)
    | '\\' :: c :: rest =>
      unless c == '\\' || c == '»' do
        return ← expected "a name escape (backslash or »)"
      out := out.push c
      chars := rest
    | '\\' :: [] => return ← expected "a name escape (backslash or »)"
    | c :: rest =>
      out := out.push c
      chars := rest

private def readName (text : String) (allowQuoted : Bool) : Except DecodeError Lean.Name := do
  if text.isEmpty then
    if allowQuoted then return .anonymous else return ← expected "a nonempty name"
  let mut chars := text.toList
  let mut name := Lean.Name.anonymous
  repeat
    if let '«' :: rest := chars then
      unless allowQuoted do return ← expected "a quoted name string"
      let (component, rest) ← readQuoted rest
      name := .str name component
      chars := rest
    else
      let (component, rest) := chars.span (· != '.')
      let component := String.ofList component
      unless isAtom component && !component.contains '.' do
        return ← expected "a nonempty atom or «quoted» name component"
      if component.all Char.isDigit then
        unless allowQuoted do return ← expected "a quoted name with numeric components"
        let some n := component.toNat? | expected "a numeric name component"
        name := .num name n
      else name := .str name component
      chars := rest
    match chars with
    | [] => return name
    | '.' :: rest =>
      if rest.isEmpty then return ← expected "a name component after the dot"
      chars := rest
    | _ => return ← expected "a dot or end of name"

@[no_expose] public instance : Fren.FromSexp Lean.Name where
  fromSexp
    | .atom a => readName a.val false
    | .string text => readName text true
    | _ => expected "a name atom or quoted name string"

end Fren.Sexp
