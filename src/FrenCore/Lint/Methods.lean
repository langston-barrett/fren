-- keep-sorted start
import FrenCore.Lint.Bools
import FrenCore.Regex
-- keep-sorted end

/-!
# Method chain, regular expression and type lints

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Methods, patterns, types and matches -/

/-- The fix of a method without arguments called on the result of another
(`lint::method_chain`). -/
inductive ChainFix where
  /-- No shorter form. -/
  | keep
  /-- `e.inner.outer` is `e`. -/
  | receiver
  /-- `e.inner.outer` is `e.m`. -/
  | single (m : Method)
  deriving Inhabited, BEq, Repr

/-- The fix of `e.inner.outer` (`lint::method_chain`). -/
def methodChain : Method → Method → ChainFix
  | .rev, .rev | .inverse, .inverse => .receiver
  | .inverse, .domain => .single .range
  | .inverse, .range => .single .domain
  | .inverse, .card => .single .card
  | .rev, .len => .single .len
  | .closure, .closure => .single .closure
  | .closure, .domain => .single .domain
  | .closure, .range => .single .range
  | _, _ => .keep

/-- Calls `m` on a chain of methods in its shortest form, given innermost
last, and rewrites the result until it is shortest again. -/
def pushMethod : List Method → Method → List Method
  | inner :: rest, m =>
    match methodChain inner m with
    | .receiver => rest
    | .single m' => pushMethod rest m'
    | .keep => m :: inner :: rest
  | [], m => [m]

/-- The shortest form of a chain of methods without arguments, innermost
first: each pair that `methodChain` shortens is rewritten, until none is. -/
def shortestChain (ms : List Method) : List Method := (ms.foldl pushMethod []).reverse

/-- A chain of methods, whose shortest form is `fixed`. -/
def methodChainMsg (fixed : String) : Msg :=
  { code? := some "F0743", headline := "this chain of methods has a shorter form"
    label? := some "means the same as a shorter chain"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- What `trivial_pattern` writes instead of `s.matches?(p)`
(`lint::trivial_pattern`). -/
inductive PatternFix where
  | equality
  | startsWith
  | endsWith
  | contains
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The string that the characters of a pattern match, if they are each a
character that is not special or `\` and a special one. -/
def literalPattern? : List Char → Option (List Char)
  | [] => some []
  | '\\' :: c :: rest => if reSpecials.contains c then (c :: ·) <$> literalPattern? rest else none
  | c :: rest => if reSpecials.contains c && c != '-' then none else (c :: ·) <$> literalPattern? rest

/-- If `trivial_pattern` fires on the pattern `p`, a string with `.*` at
its start, its end, both or neither, the fix and the string
(`lint::trivial_pattern`). -/
def trivialPattern? (p : String) : Option (PatternFix × String) := do
  let cs := p.toList
  let pre := cs.take 2 == ['.', '*']
  let cs := if pre then cs.drop 2 else cs
  let post := cs.length ≥ 2 && cs.drop (cs.length - 2) == ['.', '*']
  let lit ← literalPattern? (if post then cs.take (cs.length - 2) else cs)
  if lit.isEmpty then none
  let fix : PatternFix := match pre, post with
    | false, false => .equality
    | false, true => .startsWith
    | true, false => .endsWith
    | true, true => .contains
  return (fix, String.ofList lit)

/-- The fix of `s.matches?(p)`, from the text of `s` without parentheses
and as written, the fix and the string. -/
def trivialPatternText (recv : BText) (recvAtom : String) (fix : PatternFix) (lit : String) : BText :=
  let method (m : String) : BText := { text := s!"{recvAtom}.{m}({lit.quote})", prec := 9 }
  match fix with
  | .equality => { text := s!"{recv.inSlot (some ⟨5, .nonAssoc, false⟩)} = {lit.quote}", prec := 5 }
  | .startsWith => method "starts_with?"
  | .endsWith => method "ends_with?"
  | .contains => method "contains?"

def trivialPatternMsg (fix : PatternFix) (fixed : String) : Msg :=
  let label := match fix with
    | .equality => "matches one string"
    | .startsWith => "matches the strings that start with one"
    | .endsWith => "matches the strings that end with one"
    | .contains => "matches the strings that contain one"
  { code? := some "F0744", headline := "this pattern has no operator but `.*`", label? := some label
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- A literal of the pattern `p` that replaces `orig`: raw, with the same
delimiters, if `orig` is raw and `p` has no `"`, and otherwise with the
escapes that a literal needs. -/
def patternLiteral (orig p : String) : String :=
  if orig.startsWith "r" && !p.toList.contains '"' then
    let pre := orig.toList.takeWhile (· != '"')
    String.ofList pre ++ "\"" ++ p ++ "\"" ++ String.ofList (pre.drop 1)
  else p.quote

/-- The character that `cs`, an alternative of a pattern, matches, if it is
one character that is not special, or `\` and a special one. -/
def patternChar? : List Char → Option Char
  | ['\\', c] => if reSpecials.contains c then some c else none
  | [c] => if reSpecials.contains c && c != '-' then none else some c
  | _ => none

/-- Whether `manual_pattern_char_comparison` fires on an alternation of `n`
alternatives, from whether each is one character
(`lint::manual_pattern_char_comparison`). -/
def manualPatternCharComparison (n : Nat) (single : Bool) : Bool := n ≥ 2 && single

/-- `c` as an item of a class: `\`, `]`, `^` and `-` escaped
(`lint::class_char`). -/
def classCharText (c : Char) : String := if ['\\', ']', '^', '-'].contains c then "\\" ++ c.toString else c.toString

/-- The position after the class whose `[` is at `i` in `cs`, a pattern
that parses. -/
partial def classEnd (cs : Array Char) (i : Nat) : Nat :=
  let rec go (j : Nat) : Nat :=
    match cs[j]? with
    | none => j
    | some ']' => j + 1
    | some '\\' => go (j + 2)
    | some _ => go (j + 1)
  go (if cs[i + 1]? == some '^' then i + 2 else i + 1)

mutual
/-- The alternative of `cs` from `i` up to `|`, `)` or the end, with each
alternation of single characters in it written as a class: its text, its
text as written, and the position after it. -/
partial def charClassSeq (cs : Array Char) (i : Nat) (out : String := "") (raw : List Char := []) :
    String × List Char × Nat :=
  match cs[i]? with
  | none | some '|' | some ')' => (out, raw, i)
  | some '\\' =>
    let t := (cs.extract i (i + 2)).toList
    charClassSeq cs (i + 2) (out ++ String.ofList t) (raw ++ t)
  | some '[' =>
    let j := classEnd cs i
    let t := (cs.extract i j).toList
    charClassSeq cs j (out ++ String.ofList t) (raw ++ t)
  | some '(' =>
    let (t, j, cls) := charClassAlt cs (i + 1)
    let t := if cls then t else "(" ++ t ++ ")"
    charClassSeq cs (j + 1) (out ++ t) (raw ++ (cs.extract i (j + 1)).toList)
  | some c => charClassSeq cs (i + 1) (out.push c) (raw ++ [c])

/-- The alternation of `cs` from `i` up to `)` or the end, rewritten: its
text, the position after it, and whether it is a class. -/
partial def charClassAlt (cs : Array Char) (i : Nat) (parts : Array (String × List Char) := #[]) :
    String × Nat × Bool :=
  let (t, raw, j) := charClassSeq cs i
  let parts := parts.push (t, raw)
  if cs[j]? == some '|' then charClassAlt cs (j + 1) parts else
  let chars := parts.filterMap (patternChar? ·.2)
  if manualPatternCharComparison parts.size (chars.size == parts.size) then
    ("[" ++ String.join (chars.toList.map classCharText) ++ "]", j, true)
  else ("|".intercalate (parts.toList.map (·.1)), j, false)
end

/-- The pattern `p`, which parses, with each alternation of single
characters written as a class, if it has one
(`lint::manual_pattern_char_comparison`). -/
def charClassPattern? (p : String) : Option String :=
  let (t, _, _) := charClassAlt p.toList.toArray 0
  if t == p then none else some t

def manualPatternCharComparisonMsg (fixed : String) : Msg :=
  { code? := some Lint.manualPatternCharComparison.code, headline := "this alternation of single characters is a class"
    label? := some "matches one of several characters"
    notes := #["note: a class, such as `[abc]`, matches one character of those in it"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `almost_complete_range` fires on the range `low-high`, from the
code points of its ends, and the range of the fix
(`lint::almost_complete_range`). -/
def almostCompleteRange (low high : Int) : Bool × Int × Int :=
  let fires := ([97, 98, 65, 66].contains low && high == low + 24) || (low == 48 && high == 56)
  (fires, if fires && (low == 98 || low == 66) then low - 1 else low,
    if fires && (high == 121 || high == 89 || high == 56) then high + 1 else high)

/-- The character of a class at `i` in `cs`, which `\` may escape: the
character, its text, and the position after it. -/
def classCharAt (cs : Array Char) (i : Nat) : Char × String × Nat :=
  if cs[i]? == some '\\' then (cs[i + 1]?.getD ' ', String.ofList (cs.extract i (i + 2)).toList, i + 2)
  else (cs[i]?.getD ' ', (cs[i]?.getD ' ').toString, i + 1)

/-- The items of the class from `i` in `cs`, a pattern that parses, after
its `[` and `^`, with each range that `almost_complete_range` fires on
completed: their text, the ranges completed, and the position after the
class. -/
partial def completeClass (cs : Array Char) (i : Nat) (out : String) (found : Array (String × String)) :
    String × Array (String × String) × Nat :=
  match cs[i]? with
  | none => (out, found, i)
  | some ']' => (out.push ']', found, i + 1)
  | _ =>
    let (lo, loText, j) := classCharAt cs i
    if cs[j]? == some '-' && cs[j + 1]? != some ']' && (cs[j + 1]?).isSome then
      let (hi, hiText, k) := classCharAt cs (j + 1)
      let (fires, wlo, whi) := almostCompleteRange lo.toNat hi.toNat
      if fires then
        let whole := s!"{Char.ofNat wlo.toNat}-{Char.ofNat whi.toNat}"
        completeClass cs k (out ++ whole) (found.push (s!"{loText}-{hiText}", whole))
      else completeClass cs k (out ++ loText ++ "-" ++ hiText) found
    else completeClass cs j (out ++ loText) found

/-- The pattern `p` from `i`, with each range that `almost_complete_range`
fires on completed, and those ranges, as written and completed. -/
partial def completeRanges (cs : Array Char) (i : Nat) (out : String := "") (found : Array (String × String) := #[]) :
    String × Array (String × String) :=
  match cs[i]? with
  | none => (out, found)
  | some '\\' => completeRanges cs (i + 2) (out ++ String.ofList (cs.extract i (i + 2)).toList) found
  | some '[' =>
    let neg := cs[i + 1]? == some '^'
    let (t, found, j) := completeClass cs (if neg then i + 2 else i + 1) (if neg then "[^" else "[") found
    completeRanges cs j (out ++ t) found
  | some c => completeRanges cs (i + 1) (out.push c) found

/-- The pattern `p`, which parses, with each range that
`almost_complete_range` fires on completed, and those ranges, as written
and completed, if there is one. -/
def completeRangesPattern? (p : String) : Option (String × Array (String × String)) :=
  let (t, found) := completeRanges p.toList.toArray 0
  if found.isEmpty then none else some (t, found)

def almostCompleteRangeMsg (found : Array (String × String)) (fixed : String) : Msg :=
  let (r, whole) := found[0]!
  { code? := some Lint.almostCompleteRange.code
    headline := if found.size == 1 then s!"the range `{r}` is one character short of `{whole}`"
      else "these ranges are each one character short of a whole alphabet"
    label? := some (if found.size == 1 then s!"`{r}` leaves out one character" else "ranges that leave out one character")
    notes := #["note: a range is from its first character to its last, both included"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `literal_dot_in_pattern` fires on a `.` of a pattern, neither
escaped nor in a class, from whether a letter or digit is directly before
it, and one directly after it, neither escaped
(`lint::literal_dot_in_pattern`). -/
def literalDotInPattern (before after : Bool) : Bool := before && after

/-- The pattern `p` from `i`, which parses, with each `.` that
`literal_dot_in_pattern` fires on written `[.]`, and the text of each with
the characters around it, such as `1.2`; `lit` says that the character
before `i` is a letter or digit, not escaped. -/
partial def literalDots (cs : Array Char) (i : Nat) (lit : Bool := false) (out : String := "")
    (found : Array String := #[]) : String × Array String :=
  match cs[i]? with
  | none => (out, found)
  | some '\\' => literalDots cs (i + 2) false (out ++ String.ofList (cs.extract i (i + 2)).toList) found
  | some '[' =>
    let j := classEnd cs i
    literalDots cs j false (out ++ String.ofList (cs.extract i j).toList) found
  | some '.' =>
    let next := cs[i + 1]?.getD ' '
    if literalDotInPattern lit next.isAlphanum then
      literalDots cs (i + 1) false (out ++ "[.]") (found.push s!"{cs[i - 1]!}.{next}")
    else literalDots cs (i + 1) false (out.push '.') found
  | some c => literalDots cs (i + 1) c.isAlphanum (out.push c) found

/-- The pattern `p`, which parses, with each `.` that
`literal_dot_in_pattern` fires on written `[.]`, and the text around each,
if there is one. -/
def literalDotsPattern? (p : String) : Option (String × Array String) :=
  let (t, found) := literalDots p.toList.toArray 0
  if found.isEmpty then none else some (t, found)

def literalDotMsg (found : Array String) (fixed : String) : Msg :=
  let t := found[0]!
  { code? := some Lint.literalDotInPattern.code
    headline := if found.size == 1 then s!"the `.` in `{t}` matches any character, not only a dot"
      else "each of these `.` matches any character, not only a dot"
    label? := some (if found.size == 1 then "matches any character" else "`.` that match any character")
    notes := #[s!"note: `{t}` also matches `{t.replace "." "x"}`; `[.]` matches only a dot"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `redundant_bool_type` fires on a declaration of `n`, where
`isBool?` is whether its type, if written, is `Bool`
(`lint::redundant_bool_type`). -/
def redundantBoolType (n : Name) (isBool? : Option Bool) : Bool :=
  Fren.Str.endsWith (nameText n) "?" && isBool? == some true

def redundantBoolTypeMsg (n : Name) : Msg :=
  { code? := some "F0746", headline := s!"`{nameText n}` is a `Bool` by its name", label? := some "implied by the `?`"
    notes := #["note: a name that ends in `?` is a `Bool`, and only such a name is"]
    fixes := #[{ msg := "remove `: Bool`", replacement := "" }] }

/-- What a variable of a procedure is, as `manual_nat` sees it
(`lint::NatRole`). -/
inductive NatRole where
  | input
  | output
  | definedOutput
  deriving Inhabited, BEq, DecidableEq, Repr

/-- A variable of a procedure, as `manual_nat` sees it
(`lint::NatVariable`): its name, what it is, and whether it is declared an
`Int`. -/
structure NatVariable where
  name : String
  role : NatRole
  int : Bool
  deriving Inhabited, BEq, Repr

/-- The comparison of a conjunct, as `manual_nat` sees it
(`lint::BoundOp`): `>=`, `<=`, or another. -/
inductive BoundOp where
  | atLeast
  | atMost
  | otherOp
  deriving Inhabited, BEq, DecidableEq, Repr

def BoundOp.ofOp : String → BoundOp
  | ">=" => .atLeast
  | "<=" => .atMost
  | _ => .otherOp

/-- A conjunct of an assumption or a guarantee, as `manual_nat` sees it
(`lint::NatConjunct`): whether its constraint is an assumption, its
comparison, and the written forms of its operands. -/
structure NatConjunct where
  assumption : Bool
  op : BoundOp
  left : String
  right : String
  deriving Inhabited, BEq, Repr

/-- Whether the conjunct `c` is a bound of `v` that `manual_nat` reports
(`lint::bounds?`): `v` is declared an `Int`, `c` says that it is at least
`0`, and `c` is an assumption of an input or a guarantee of an output that
is not defined. -/
def natBounds (v : NatVariable) (c : NatConjunct) : Bool :=
  v.int
    && (match c.op with
      | .atLeast => c.left == v.name && c.right == "0"
      | .atMost => c.left == "0" && c.right == v.name
      | .otherOp => false)
    && (match v.role with
      | .input => c.assumption
      | .output => !c.assumption
      | .definedOutput => false)

/-- The position in `cs`, the conjuncts of a procedure's assumptions and
guarantees in order, of the bound of `v` that `manual_nat` reports, if it
fires, where `kept` says that a call, a refinement or an `impl` in
the file gives `v` an `Int` (`lint::manual_nat`). -/
def manualNatAt (v : NatVariable) (cs : List NatConjunct) (kept : Bool) : Option Nat :=
  if kept then none else cs.findIdx? (natBounds v)

/-- Where `manual_nat` fires in a procedure, given its own variables and
the conjuncts of each of its assumptions and guarantees, before the end of
the file shows which variables are kept `Int`s: for each variable it
fires on, its position, and the constraint and conjunct of its bound. -/
def manualNatBounds (vars : Array NatVariable) (props : Array (Array NatConjunct)) : Array (Nat × Nat × Nat) :=
  let flat := props.toList.zipIdx.flatMap fun (cs, p) => cs.toList.zipIdx.map fun (c, k) => (c, p, k)
  vars.zipIdx.filterMap fun (v, i) => do
    let j ← manualNatAt v (flat.map (·.1)) false
    let (_, p, k) ← flat[j]?
    return (i, p, k)

/-- A type that a file gives a variable of a procedure, by a call's,
a refinement's or an `impl`'s binding, or a refinement that reads it by
name (`lint::Given`). -/
inductive Given where
  | givenInt
  | givenNat
  deriving Inhabited, DecidableEq, Repr

/-- `manual_nat` on the variable `x`, whose bound `bound` is a conjunct of
the constraint `prop`. -/
def manualNatMsg (x : String) (input : Bool) (prop bound : String) : Msg :=
  let kind := if input then "assumption" else "guarantee"
  { code? := some Lint.manualNat.code, headline := s!"`{x}` is never negative, so it can be a `Nat`"
    label? := some s!"`{x}` is at least 0 by this {kind}"
    notes := #[s!"note: a `Nat` {if input then "parameter" else "output"} brings this {kind} with its type"]
      ++ (if input then #[s!"note: a call must then pass a `Nat` for `{x}`"] else #[])
      ++ #[s!"help: declare `{x}: Nat`, and remove `{bound}` from `{prop}`, where nothing binds `{x}` to an `Int`"] }

/-- Whether `trivial_match` fires on a `match` of `nArms` arms, whose first
binds a name if `binds` (`lint::trivial_match`). -/
def trivialMatch (nArms : Nat) (binds : Bool) : Bool := nArms == 1 && !binds

/-- A `match` of one arm, whose body, as the fix writes it, is `fixed`. -/
def trivialMatchMsg (fixed : String) : Msg :=
  { code? := some "F0747", headline := "this `match` has one arm, which binds nothing"
    label? := some "always its only arm"
    notes := #["note: its value is the arm's body, whatever the scrutinee is"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `zero_sized_map_values` fires on `Rel<A, B>`, where `B` is an
enumeration of `nVariants` if `enum`, of which some has a payload if
`payload` (`lint::zero_sized_map_values`). -/
def zeroSizedMapValues (enum : Bool) (nVariants : Nat) (payload : Bool) : Bool :=
  enum && nVariants == 1 && !payload

/-- `Rel<a, b>`, where `v` is the one variant of `b`. -/
def zeroSizedMapValuesMsg (a b v : String) : Msg :=
  { code? := some "F0789", headline := s!"`Rel<{a}, {b}>` relates to `{b}`, which has one value"
    label? := some s!"`{b}` has only `{b}::{v}`"
    notes := #[s!"note: such a relation says only which `{a}`s it relates, as a set does",
      s!"help: write `Set<{a}>`"] }

end Fren.Core
