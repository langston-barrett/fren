-- keep-sorted start
import FrenCore.Diagnostic
-- keep-sorted end

/-!
# Identifiers

How both front ends read identifiers (`Reqs/Lang/Lexical#identifiers`): the
`fren` command's lexer scans them with these, and the Lean front end, which
Lean's lexer feeds, checks each identifier with `identifierAccepted`. Lean's
identifiers are a superset of Fren's, so both report the lexemes that Lean
would read as one identifier but Fren would not.
-/

namespace Fren.Core

/-- `[A-Za-z_]`: starts an identifier (`lang::identifier`). -/
def isIdStart (c : Char) : Bool := ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || c == '_'

/-- `[A-Za-z0-9_']`: continues an identifier. -/
def isIdRest (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '_' || c == '\''

/-- How many characters at `i` continue an identifier whose last character
is `last`, or `0` where it ends (`lang::identifier_end`): a character of an
identifier, a final `?`, or a `.` and the start of another component. -/
def identExtends (src : Array Char) (last : Char) (i : Nat) : Nat :=
  if last == '?' then 0 else
  match src[i]? with
  | some c =>
    if isIdRest c || c == '?' then 1
    else if c == '.' && (src[i + 1]?).any isIdStart then 2
    else 0
  | none => 0

/-- Where the identifier that starts at `i` ends: like Lean, `a.b` is one
identifier, of two components (`lang::identifier`). -/
def identEnd (src : Array Char) (i : Nat) : Nat := go src[i]! (i + 1)
where
  go (last : Char) (j : Nat) : Nat :=
    if _h : j < src.size then
      match identExtends src last j with
      | 0 => j
      | k + 1 => go src[j + k]! (j + k + 1)
    else j
  termination_by src.size - j

/-- Whether `s` is an identifier: the lexer reads all of it as one
(`lang::identifier`). -/
def identifierAccepted (s : String) : Bool :=
  let a := s.toList.toArray
  match a[0]? with
  | some c => isIdStart c && identEnd a 0 == a.size
  | none => false

/-- Where Lean's lexer ends the identifier that starts at `i`, of the
characters that Fren allows: Lean also allows `?` and `!` anywhere after the
first character. -/
def leanIdentEnd (src : Array Char) (i : Nat) : Nat := go (i + 1)
where
  go (j : Nat) : Nat :=
    if _h : j < src.size then
      let c := src[j]
      if isIdRest c || c == '?' || c == '!' then go (j + 1)
      else if c == '.' && (src[j + 1]?).any isIdStart then go (j + 2)
      else j
    else j
  termination_by src.size - j

/-- An identifier that Lean reads, but that is not one of Fren's. -/
def leanIdentifierMsg (s : String) : Msg :=
  { code? := some "F0119", headline := s!"`{s}` is not an identifier in Fren", label? := some "not a Fren identifier"
    notes := #["note: an identifier is ASCII letters, digits, `_` and `'`, with `.` between components and an optional `?` at the end"]
      ++ if s.contains '!' then #["help: `!` is not part of an identifier; to compare, write `a != b`, with spaces"] else #[] }

end Fren.Core
