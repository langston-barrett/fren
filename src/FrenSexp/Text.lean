module

public import FrenSexp.Basic

namespace Fren.Sexp

private def quoteString (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := out ++ match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\t' => "\\t"
      | c => String.singleton c
  return out ++ "\""

/-- Canonical one-line text. Only quote, backslash, LF and tab are escaped. -/
public partial def render : Sexp → String
  | .atom a => a.val
  | .string s => quoteString s
  | .list xs => "(" ++ " ".intercalate (xs.toList.map render) ++ ")"

private def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

private partial def prettyAt (value : Sexp) (column : Nat) : String := Id.run do
  let flat := render value
  if column + flat.length <= 80 then return flat
  match value with
  | .list xs =>
    if xs.isEmpty then return "()"
    let mut out := "(" ++ prettyAt xs[0]! (column + 1)
    for x in xs.toList.drop 1 do
      out := out ++ "\n" ++ spaces (column + 2) ++ prettyAt x (column + 2)
    let lines := out.splitOn "\n"
    let lastWidth := (lines.getLast!).length + if lines.length == 1 then column else 0
    if lastWidth >= 80 then return out ++ "\n" ++ spaces column ++ ")"
    return out ++ ")"
  | _ => return flat

/-- Lists fitting in 80 columns at their indentation stay on one line.
Otherwise the head follows `(` and each remaining child starts a new line,
indented two spaces. A closing parenthesis moves to its list's indentation
when needed. Indivisible atoms and strings can exceed the limit. -/
public def pretty (value : Sexp) : String := prettyAt value 0

private structure Cursor where
  chars : Array Char
  index : Nat := 0
  position : Position := {}

private def Cursor.peek (s : Cursor) : Option Char := s.chars[s.index]?

private def Cursor.next (s : Cursor) : Cursor :=
  match s.peek with
  | none => s
  | some c => { s with
      index := s.index + 1
      position := {
        byteOffset := s.position.byteOffset + (String.singleton c).utf8ByteSize
        line := if c == '\n' then s.position.line + 1 else s.position.line
        column := if c == '\n' then 1 else s.position.column + 1 } }

private def whitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def skip (s : Cursor) : Cursor := Id.run do
  let mut s := s
  let mut comment := false
  while let some c := s.peek do
    if comment then
      s := s.next
      if c == '\n' then comment := false
    else if c == ';' then
      comment := true
      s := s.next
    else if whitespace c then s := s.next
    else break
  return s

private def fail (s : Cursor) (expected : String) : Except ParseError α :=
  .error { position := s.position, expected }

private def parseString (s : Cursor) : Except ParseError (String × Cursor) := do
  let mut s := s
  let mut out := ""
  while let some c := s.peek do
    if c == '"' then return (out, s.next)
    if c == '\\' then
      s := s.next
      let some escaped := s.peek | fail s "a string escape (quote, backslash, n or t)"
      let decoded ← match escaped with
        | '"' => pure '"'
        | '\\' => pure '\\'
        | 'n' => pure '\n'
        | 't' => pure '\t'
        | _ => fail s "a string escape (quote, backslash, n or t)"
      out := out.push decoded
      s := s.next
    else
      out := out.push c
      s := s.next
  fail s "a closing double quote"

private partial def parseValue (s : Cursor) : Except ParseError (Located × Cursor) := do
  let s := skip s
  let start := s.position
  match s.peek with
  | none => fail s "an atom, string or list"
  | some '(' =>
    let mut s := s.next
    let mut values := #[]
    let mut locations := #[]
    repeat
      s := skip s
      match s.peek with
      | none => return ← fail s "a closing parenthesis"
      | some ')' =>
        return (⟨.list values, .node start locations⟩, s.next)
      | _ =>
        let (child, rest) ← parseValue s
        values := values.push child.value
        locations := locations.push child.locations
        s := rest
  | some '"' =>
    let (text, rest) ← parseString s.next
    return (⟨.string text, .node start #[]⟩, rest)
  | some c =>
    unless isAtomChar c do return ← fail s "an atom, string or list"
    let mut s := s
    let mut word := ""
    while s.peek.any isAtomChar do
      word := word.push s.peek.get!
      s := s.next
    let some a := Atom.ofString? word | fail s "a nonempty ASCII atom"
    return (⟨.atom a, .node start #[]⟩, s)

/-- Read exactly one expression, retaining locations for typed decoding. -/
public def parseLocated (text : String) : Except ParseError Located := do
  let (value, rest) ← parseValue { chars := text.toList.toArray }
  let rest := skip rest
  if rest.peek.isSome then fail rest "end of input" else return value

public def parse (text : String) : Except ParseError Sexp :=
  (parseLocated text).map (·.value)

end Fren.Sexp
