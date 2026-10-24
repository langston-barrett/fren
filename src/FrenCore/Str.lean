/-!
# Strings

The meaning of Fren's `String` methods (`Reqs/Lang/Expressions#methods`),
shared by the Lean front end, which maps each method to its definition
here, and the `fren` command's evaluator. Each is total, with SMT-LIB's
values at the edges, and positions are `Int`s, as in Fren. Literals are
written for SMT-LIB and read back from its models here too, so that both
front ends agree on them.
-/

namespace Fren.Str

/-- A literal of a spec. The identity, so that the solver's translation can
write the literal itself, escaped as SMT-LIB needs (`Fren.Core.smtStringLit`). -/
@[reducible] def lit (s : String) : String := s

/-- `s.len`: SMT-LIB's `str.len`. -/
def len (s : String) : Int := s.length

/-- `s.starts_with?(p)`: SMT-LIB's `str.prefixof p s`. -/
def startsWith (s p : String) : Bool := p.toList.isPrefixOf s.toList

/-- `s.ends_with?(p)`: SMT-LIB's `str.suffixof p s`. -/
def endsWith (s p : String) : Bool := p.toList.isSuffixOf s.toList

/-- `s.contains?(t)`: SMT-LIB's `str.contains s t`; every string contains `""`. -/
def contains (s t : String) : Bool :=
  (List.range (s.length + 1)).any fun i => t.toList.isPrefixOf (s.toList.drop i)

/-- `s.slice(i, n)`: SMT-LIB's `str.substr`; `""` unless `0 ≤ i < |s|` and
`0 < n`. -/
def slice (s : String) (i n : Int) : String :=
  if 0 ≤ i ∧ i < s.length ∧ 0 < n then String.ofList ((s.toList.drop i.toNat).take n.toNat) else ""

/-- `s.at(i)`: SMT-LIB's `str.at`, which is `str.substr s i 1`. -/
def «at» (s : String) (i : Int) : String := slice s i 1

/-- `s.index_of(t, i)`: SMT-LIB's `str.indexof`; `-1` unless `0 ≤ i ≤ |s|`
and `t` occurs at or after `i`, and `i` if `t` is `""`. -/
def indexOf (s t : String) (i : Int) : Int :=
  if 0 ≤ i ∧ i ≤ s.length then
    match (List.range (s.length + 1 - i.toNat)).find? fun k => t.toList.isPrefixOf (s.toList.drop (i.toNat + k)) with
    | some k => i + k
    | none => -1
  else -1

/-- `s.replace(a, b)`: SMT-LIB's `str.replace`: the first occurrence only, and
`b ++ s` if `a` is `""`. -/
def replace (s a b : String) : String :=
  if a.isEmpty then b ++ s else
    let j := indexOf s a 0
    if j < 0 then s else
      String.ofList (s.toList.take j.toNat ++ b.toList ++ s.toList.drop (j.toNat + a.length))

/-- Replaces each occurrence of `a`, which is not empty, in `cs`, from the
left, within `fuel` steps. -/
def replaceAllAux : Nat → List Char → List Char → List Char → List Char
  | 0, cs, _, _ => cs
  | _ + 1, [], _, _ => []
  | fuel + 1, c :: rest, a, b =>
    if a.isPrefixOf (c :: rest) then b ++ replaceAllAux fuel ((c :: rest).drop a.length) a b
    else c :: replaceAllAux fuel rest a b

/-- `s.replace_all(a, b)`: SMT-LIB's `str.replace_all`: every occurrence,
from the left and not overlapping, and `s` if `a` is `""`. -/
def replaceAll (s a b : String) : String :=
  if a.isEmpty then s else String.ofList (replaceAllAux (s.length + 1) s.toList a.toList b.toList)

theorem startsWith_iff (s p : String) : startsWith s p = true ↔ p.toList <+: s.toList :=
  List.isPrefixOf_iff_prefix

theorem endsWith_iff (s p : String) : endsWith s p = true ↔ p.toList <:+ s.toList :=
  List.isSuffixOf_iff_suffix

end Fren.Str

namespace Fren.Core

/-- U+2FFFF, the last character of SMT-LIB's strings (`lang::MAX_CHAR`). -/
def maxChar : Nat := 196607

/-- Whether a literal may contain the character with code point `code`
(`lang::string_char`). -/
def stringCharAccepted (code : Int) : Bool := code ≤ maxChar

/-- `s` as an SMT-LIB 2.6 string literal: `"` is `""`, and `\` and every
character outside printable ASCII is `\u{h}`, since SMT-LIB reads
`\u{...}` inside a literal (`Reqs/Cli`). -/
def smtStringLit (s : String) : String :=
  let body := s.foldl (init := "") fun acc c =>
    if c == '"' then acc ++ "\"\""
    else if c == '\\' || c.toNat < 32 || c.toNat > 126 then
      acc ++ "\\u{" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ "}"
    else acc.push c
  "\"" ++ body ++ "\""

/-- The string that the SMT-LIB literal `lit` stands for, as cvc5 prints
it in a model: `""` for `"`, and `\u{h}`, `\uhhhh` or `\u{hhhhh}` escapes. -/
partial def parseSmtString? (lit : String) : Option String := do
  let cs := lit.toList
  guard (cs.length ≥ 2 && cs.head? == some '"' && cs.getLast? == some '"')
  let hexVal (ds : List Char) : Option Nat :=
    ds.foldlM (init := 0) fun acc d =>
      if d.isDigit then some (acc * 16 + (d.toNat - '0'.toNat))
      else if 'a' ≤ d.toLower && d.toLower ≤ 'f' then some (acc * 16 + (d.toLower.toNat - 'a'.toNat + 10))
      else none
  let rec go : List Char → String → Option String
    | [], acc => some acc
    | '"' :: '"' :: rest, acc => go rest (acc.push '"')
    | '\\' :: 'u' :: '{' :: rest, acc =>
      let ds := rest.takeWhile (· != '}')
      match rest.drop ds.length, hexVal ds with
      | '}' :: rest', some v => if ds.isEmpty then none else go rest' (acc.push (Char.ofNat v))
      | _, _ => none
    | '\\' :: 'u' :: a :: b :: c :: d :: rest, acc =>
      match hexVal [a, b, c, d] with
      | some v => go rest (acc.push (Char.ofNat v))
      | none => go (a :: b :: c :: d :: rest) (acc ++ "\\u")
    | c :: rest, acc => go rest (acc.push c)
  go ((cs.drop 1).dropLast) ""

end Fren.Core
