-- keep-sorted start
import FrenCli.Quote
import FrenCore.Lint.Operators
-- keep-sorted end

/-!
# Operator and method lint checks

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-- `double_comparison` on `n`, an `and` or an `or`, in `slot` within
`parent` (`lint::double_comparison`). -/
def doubleComparisonAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) (conj : Bool) :
    Option (OpReport α) := do
  let #[l, r] := n.kids | none
  let .bin lop := l.kind | none
  let .bin rop := r.kind | none
  let #[a, b] := l.kids | none
  let op ← if lop == "subset" && rop == "subset" then do
      let #[c, d] := r.kids | none
      -- `a subset b and b subset a`.
      unless conj && writtenForm (textOf src c.range) == writtenForm (textOf src b.range)
        && writtenForm (textOf src d.range) == writtenForm (textOf src a.range) do none
      pure "="
    else do
      let (c1, a1, b1) ← comparisonOf? src l
      let (c2, a2, b2) ← comparisonOf? src r
      let c2 ← if a2 == a1 && b2 == b1 then pure c2 else if a2 == b1 && b2 == a1 then pure c2.mirror else none
      pure (← doubleComparison conj c1 c2).op
  let fixed := placed src n slot parent (binText op (a.text src) (b.text src))
  return { lint := .doubleComparison, ref := n.ref, msg := doubleComparisonMsg fixed }

/-- `bool_equality` on `n`, a comparison in `slot` within `parent`, where
`boolEq` says whether a comparison's operands are `Bool`s. -/
def boolEqualityAt? (src : Array Char) (boolEq : α → Bool) (n : BNode α) (slot : Option Slot) (parent : Range) :
    Option (OpReport α) := do
  let .bin op := n.kind | none
  let c ← Comparison.ofOp? op
  let #[a, b] := n.kids | none
  unless boolEquality c (boolEq n.ref) (a.kind matches .lit _ || b.kind matches .lit _) do none
  let fixed := placed src n slot parent (binText "iff" (a.text src) (b.text src))
  return { lint := .boolEquality, ref := n.ref, msg := boolEqualityMsg fixed }

/-- `manual_method` on `n`, a comparison in `slot` within `parent`
(`lint::index_test`, `lint::one_character`). -/
def manualMethodAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  let .bin op := n.kind | none
  let c ← Comparison.ofOp? op
  let #[a, b] := n.kids | none
  -- The call, the other operand, and the comparison with the call on the left.
  let (call, other, c) := if a.kind matches .method _ then (a, b, c) else (b, a, c.mirror)
  let .method m := call.kind | none
  let recv ← call.kids[0]?
  let r := operandText src call.range recv
  let report (method fixed : String) (prec : Nat) (label : String) : OpReport α :=
    let fixed := placed src n slot parent { text := fixed, prec }
    { lint := .manualMethod, ref := n.ref, msg := manualMethodMsg method fixed label }
  -- `s.at(0) = t` and `s.at(s.len - 1) = t`, where `t` has one character.
  if m == "at" then
    let #[_, i] := call.kids | none
    unless (c == .eq || c == .ne) && oneElement src other do none
    let o := writtenForm (textOf src recv.range)
    let last := match i.kind, i.kids with
      | .bin "-", #[l, one] => writtenForm (textOf src one.range) == "1" && isLenOf src o l
      | _, _ => false
    let method ← if writtenForm (textOf src i.range) == "0" then some "starts_with?" else if last then some "ends_with?" else none
    let call := s!"{r}.{method}({textOf src other.range})"
    let label := if last then "compares the last element" else "compares the first element"
    return if c == .eq then report method call (BKind.method "").prec label
      else report method s!"not {call}" BKind.not.prec label
  let #[_, x, y] := call.kids | none
  if m == "index_of" then
    unless writtenForm (textOf src y.range) == "0" do none
    let t := textOf src x.range
    match indexTest c (← intLiteral? src other) with
    | .found => return report "contains?" s!"{r}.contains?({t})" (BKind.method "").prec "compares a position"
    | .absent => return report "contains?" s!"not {r}.contains?({t})" BKind.not.prec "compares a position"
    | .atStart => return report "starts_with?" s!"{r}.starts_with?({t})" (BKind.method "").prec "compares a position"
    | .other => none
  -- `s.slice(0, t.len) = t`.
  unless m == "slice" && c == .eq && writtenForm (textOf src x.range) == "0" do none
  unless isLenOf src (writtenForm (textOf src other.range)) y do none
  return report "starts_with?" s!"{r}.starts_with?({textOf src other.range})" (BKind.method "").prec "compares a prefix"

/-- `length_zero` on `n`, `s.at(0) = ""` or `q.at(0) = []`, or `!=`, in
`slot` within `parent` (`lint::first_empty`). -/
def firstEmptyAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  let .bin op := n.kind | none
  unless op == "=" || op == "!=" do none
  let #[a, b] := n.kids | none
  let (call, other) := if a.kind matches .method _ then (a, b) else (b, a)
  let .method m := call.kind | none
  let #[recv, i] := call.kids | none
  let empty := writtenForm (textOf src other.range)
  unless m == "at" && writtenForm (textOf src i.range) == "0" && (empty == "\"\"" || empty == "[]") do none
  let fixed := placed src n slot parent (binText op (recv.text src) { text := empty, prec := BKind.atom.prec })
  return { lint := .lengthZero, ref := n.ref, msg := firstEmptyMsg fixed empty }

/-- Whether `redundant_slicing` fires on `s.slice(i, n)`, from whether it is
written `s.slice(0, s.len)`, the receivers written the same
(`lint::redundant_slicing`). -/
def redundantSlicing (whole : Bool) : Bool := whole

/-- Whether `no_effect_replace` fires on `s.replace(a, b)` or
`s.replace_all(a, b)`, from whether `a` and `b` are written the same
(`lint::no_effect_replace`). -/
def noEffectReplace (same : Bool) : Bool := same

/-- `manual_method` on `s.slice(i, 1)`, `redundant_slicing` on `s.slice(0,
s.len)`, and `no_effect_replace` on `s.replace(a, a)` and
`s.replace_all(a, a)`, where `n` is the call, in `slot` within `parent`
(`lint::one_character`, `lint::redundant_slicing`,
`lint::no_effect_replace`). -/
def methodCallAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  let .method m := n.kind | none
  let recv ← n.kids[0]?
  let receiver := placed src n slot parent (recv.text src)
  match m, n.kids with
  | "slice", #[_, i, k] =>
    if writtenForm (textOf src k.range) == "1" then
      let fixed := s!"{operandText src n.range recv}.at({textOf src i.range})"
      return { lint := .manualMethod, ref := n.ref, msg := manualMethodMsg "at" fixed "a slice of length 1" }
    unless redundantSlicing (writtenForm (textOf src i.range) == "0" && isLenOf src (writtenForm (textOf src recv.range)) k) do none
    return { lint := .redundantSlicing, ref := n.ref, msg := redundantSlicingMsg receiver }
  | "replace", #[_, a, b] | "replace_all", #[_, a, b] =>
    unless noEffectReplace (writtenSame (textOf src a.range) (textOf src b.range)) do none
    return { lint := .noEffectReplace, ref := n.ref, msg := noEffectReplaceMsg m receiver }
  | _, _ => none

/-- The least value of `n`, a call of a method whose values have a least
one, and the method (`Reqs/Lint/Pedantic#ranges-of-methods`): `index_of`,
which is never below `-1`, and `abs`, never below `0`, which `isAbs` says
`n` is, since `x.abs` is written as a field read is. -/
def leastValue? (isAbs : α → Bool) (n : BNode α) : Option (String × Int) :=
  match n.kind, n.kids.size with
  | .method "index_of", 3 => some ("index_of", -1)
  | .atom, _ | .method "abs", 1 => if isAbs n.ref then some ("abs", 0) else none
  | _, _ => none

/-- Whether `invalid_upcast_comparisons` fires on a comparison of a call
that is never below `least` with `bound`, `call OP bound` if `callLeft` and
`bound OP call` otherwise, and what it always is where it fires
(`lint::invalid_upcast_comparisons`): the call is above `bound`, or, for
`least`, the same or above. -/
def invalidUpcast (op : Comparison) (bound least : Int) (callLeft : Bool) : Bool × Bool :=
  match if callLeft then op else op.mirror with
  | .lt => (bound ≤ least, false)
  | .ge => (bound ≤ least, true)
  | .eq | .le => (bound < least, false)
  | .ne | .gt => (bound < least, true)

/-- A comparison of a call of `method`, never below `least`, that is always
`value`. -/
def invalidUpcastMsg (method : String) (least : Int) (value : Bool) : Msg :=
  { code? := some Lint.invalidUpcastComparisons.code, headline := s!"this comparison is always `{value}`"
    label? := some s!"`{method}` is never below {least}"
    notes := #["note: the bound or the operator is probably not the one meant"] }

/-- `invalid_upcast_comparisons` on `n`, a comparison, where `isAbs` says
which expressions are calls of `abs` (`lint::invalid_upcast_comparisons`). -/
def invalidUpcastAt? (src : Array Char) (isAbs : α → Bool) (n : BNode α) : Option (OpReport α) := do
  let .bin op := n.kind | none
  let c ← Comparison.ofOp? op
  let #[a, b] := n.kids | none
  let (call, other, left) := if (leastValue? isAbs a).isSome then (a, b, true) else (b, a, false)
  let (method, least) ← leastValue? isAbs call
  let (fires, value) := invalidUpcast c (← intLiteral? src other) least left
  unless fires do none
  return { lint := .invalidUpcastComparisons, ref := n.ref, msg := invalidUpcastMsg method least value }

/-- The `else` branch that ends a conditional: of the last conditional in a
chain of `else if`s written without parentheses. -/
partial def lastElse (src : Array Char) (n : BNode α) : Option (BNode α) := do
  let #[_, _, e] := n.kids | none
  if e.kind == .ite && !enclosed src n.range e.range then lastElse src e else some e

/-- `else_extends` on the operand `k`, a conditional, of `n`, a binary
operator, in `slot` (`lint::else_extends`). -/
def elseExtendsAt? (src : Array Char) (n k : BNode α) (slot : Slot) : Option (OpReport α) := do
  let .bin op := n.kind | none
  unless k.kind == .ite && !enclosed src n.range k.range do none
  let e ← lastElse src k
  unless !enclosed src k.range e.range && elseExtends slot.outer e.kind.prec slot.assoc slot.right do none
  let branch := textOf src e.range
  let fixed := textOf src { start := k.range.start, stop := e.range.start } ++ s!"({branch})"
    ++ textOf src { start := e.range.stop, stop := k.range.stop }
  return { lint := .elseExtends, ref := k.ref, msg := elseExtendsMsg op branch fixed }

/-- Whether the text of `src` in `r` (`textOf`) has more than two
characters other than whitespace, and no `-` or `/`. Then it has no
comment, so `writtenForm` keeps each of those characters, and its form is
longer than two characters. -/
def formLongerThanTwo (src : Array Char) (r : Range) : Bool :=
  go (min r.stop src.size) r.start 0
where
  go (stop i seen : Nat) : Bool :=
    if h : i < stop then
      let c := src[i]!
      if c == '-' || c == '/' then false
      else if c.isWhitespace then go stop (i + 1) seen
      else if seen == 2 then
        -- A third character; the rest of the text must still have no `-`
        -- or `/`, since a comment could start there.
        rest stop (i + 1)
      else go stop (i + 1) (seen + 1)
    else false
  termination_by stop - i
  rest (stop i : Nat) : Bool :=
    if h : i < stop then
      let c := src[i]!
      if c == '-' || c == '/' then false else rest stop (i + 1)
    else true
  termination_by stop - i

/-- How `identity_op` sees the operand `k`. -/
def identityOperand (src : Array Char) (k : BNode α) : IdentityOperand :=
  match k.kind with
  | .neg => .negation
  -- Only an atom's text is read, and not even that when it is surely
  -- longer than the forms below (`formLongerThanTwo`).
  | .atom => if formLongerThanTwo src k.range then .other else match writtenForm (textOf src k.range) with
    | "0" => .zero
    | "1" => .one
    | "\"\"" | "[]" | "{}" => .empty
    | _ => .other
  | _ => .other

/-- `identity_op` on `n`, a binary operator in `slot` within `parent`
(`lint::identity_op`). -/
def identityOpAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  let .bin op := n.kind | none
  let o ← IdentityOperator.ofOp? op
  let #[a, b] := n.kids | none
  let (t, flip) ← match identityRewrite o (identityOperand src a) (identityOperand src b) with
    | .keepLeft => some (a.text src, false)
    | .keepRight => some (b.text src, false)
    | .flip =>
      let y ← b.kids[0]?
      some (binText (if o == .add then "-" else "+") (a.text src) (y.text src), true)
    | .unchanged => none
  let fixed := placed src n slot parent t
  return { lint := .identityOp, ref := n.ref, msg := identityOpMsg fixed flip }

/-- Whether `needless_bool_assign` fires on `if C then A else B`, and
whether its fix is `C != X`, rather than `C iff X`, where `elseNegates`
says that `B` is `not X`, for an `X` written the same as `A`, and
`thenNegates` that `A` is `not X`, for an `X` written the same as `B`
(`lint::needless_bool_assign`). -/
def needlessBoolAssign (elseNegates thenNegates : Bool) : Bool × Bool := (elseNegates || thenNegates, !elseNegates)

/-- `if C then X else not X`, or `if C then not X else X` if `unequal`,
where `x` is the text of `X`, as the text of its fix. -/
def needlessBoolAssignMsg (x fixed : String) (unequal : Bool) : Msg :=
  { code? := some Lint.needlessBoolAssign.code, headline := "this `if` gives a `Bool` or its negation"
    label? := some (if unequal then s!"the negation of `{x}` if the condition holds, and `{x}` otherwise"
      else s!"`{x}` if the condition holds, and its negation otherwise")
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `needless_bool_assign` on `n`, a conditional in `slot` within `parent`
(`lint::needless_bool_assign`). -/
def needlessBoolAssignAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) :
    Option (OpReport α) := do
  let #[c, a, b] := n.kids | none
  -- Whether `k` is `not X`, for an `X` written the same as `x`.
  let negates (k x : BNode α) : Bool := match k.kind, k.kids with
    | .not, #[y] => writtenSame (textOf src y.range) (textOf src x.range)
    | _, _ => false
  let (fires, unequal) := needlessBoolAssign (negates b a) (negates a b)
  unless fires do none
  let x := if unequal then b else a
  let fixed := placed src n slot parent (binText (if unequal then "!=" else "iff") (c.text src) (x.text src))
  return { lint := .needlessBoolAssign, ref := n.ref, msg := needlessBoolAssignMsg (textOf src x.range) fixed unequal }

/-- Whether `branches_sharing_code` fires on `if C then A op X else B op X`,
or `X op A` and `X op B`, from whether both branches apply the same binary
operator, whether their left, and their right, operands are written the
same, both being `same_branches`, and whether the fix would be `nonlinear`
(`branchesSharingNonlinear`) (`lint::branches_sharing_code`). -/
def branchesSharingCode (sameOp sharedLeft sharedRight nonlinear : Bool) : Bool :=
  sameOp && sharedLeft != sharedRight && !nonlinear

/-- Whether the fix of `branches_sharing_code` for the operator `op`, whose
shared operand is on the left if `left`, is outside the arithmetic that
Fren accepts: for `*`, the product of the `if` that the fix moves out,
which mentions `ifMentioned`, with the shared operand, which mentions
`sharedMentioned`, is not accepted (`lang::linear_product`); for `div` and
`mod`, the `if` would be the divisor, which must be a literal or a
constant (`lang::divisor`). -/
def branchesSharingNonlinear (op : String) (left : Bool) (ifMentioned sharedMentioned : List Mention) : Bool :=
  if op == "div" || op == "mod" then left else op == "*" && !productAccepted ifMentioned sharedMentioned

/-- `if C then A op X else B op X`, or the mirror form if `left`, whose
shared operand is written `x`, as the text of its fix. -/
def branchesSharingCodeMsg (op x fixed : String) (left : Bool) : Msg :=
  { code? := some Lint.branchesSharingCode.code
    headline := if left then s!"both branches of this `if` start with `{x} {op}`"
      else s!"both branches of this `if` end with `{op} {x}`"
    label? := some "the same operand in both branches"
    notes := #[s!"note: `{x}` is evaluated whichever branch is taken, and has the same value in both"]
    fixes := #[{ msg := "move it out of the `if`", replacement := fixed }] }

/-- `branches_sharing_code` on `n`, a conditional in `slot` within `parent`,
where `mentioned` is what an expression mentions, as far as the lint needs
it: what a condition or an operand of `*` mentions
(`lint::branches_sharing_code`). -/
def branchesSharingAt? (src : Array Char) (mentioned : α → List Mention) (n : BNode α) (slot : Option Slot) (parent : Range) :
    Option (OpReport α) := do
  let #[c, a, b] := n.kids | none
  let .bin op := a.kind | none
  let #[a1, a2] := a.kids | none
  let #[b1, b2] := b.kids | none
  let same (x y : BNode α) := writtenSame (textOf src x.range) (textOf src y.range)
  let left := same a1 b1
  -- The operands that the fix moves into an `if`, and the shared one.
  let (ka, kb, kx) := if left then (a2, b2, a1) else (a1, b1, a2)
  let nonlinear := branchesSharingNonlinear op left (mentioned c.ref ++ mentioned ka.ref ++ mentioned kb.ref) (mentioned kx.ref)
  unless branchesSharingCode (b.kind == .bin op) left (same a2 b2) nonlinear do none
  let k := BKind.bin op
  -- The branches without the shared operand, with the parentheses they are written with.
  let (x, ta, tb) := if left then (operandText src a.range a1, operandText src a.range a2, operandText src b.range b2)
    else (operandText src a.range a2, operandText src a.range a1, operandText src b.range b1)
  let ite : BText := { text := s!"if {textOf src c.range} then {ta} else {tb}", prec := BKind.ite.prec }
  let text := if left then s!"{x} {op} {ite.inSlot (k.slots[1]?.join)}" else s!"{ite.inSlot (k.slots[0]?.join)} {op} {x}"
  let fixed := placed src n slot parent { text, prec := k.prec }
  return { lint := .branchesSharingCode, ref := n.ref, msg := branchesSharingCodeMsg op x fixed left }

/-- The binary operators that are punctuators, but `-`, which
`suspicious_unary_op_formatting` looks at: `-` is never directly followed
by a `-`, which would start a comment, and `<` never is, since `<-` is
one punctuator. -/
def punctuatorOps : Array String := #["=", "!=", "<=", ">", ">=", "+", "++", "*"]

/-- Whether `suspicious_unary_op_formatting` fires on `a OP -b`, from
whether `OP` is a punctuator other than `-`, the `-` follows it directly,
and whitespace follows the `-` (`lint::suspicious_unary_op_formatting`). -/
def suspiciousUnaryOp (punctuator adjacent spaced : Bool) : Bool := punctuator && adjacent && spaced

def suspiciousUnaryOpMsg (op fixed : String) : Msg :=
  { code? := some Lint.suspiciousUnaryOpFormatting.code, headline := s!"`{op}-` looks like one operator"
    label? := some s!"`{op}`, then a negation"
    notes := #[s!"note: there is no operator `{op}-`: this is `{op}`, whose right operand is negated"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `suspicious_unary_op_formatting` on `n`, a binary operator
(`lint::suspicious_unary_op_formatting`). The fix moves the whitespace
after the `-` to before it, but keeps a space after it before a `-`,
which would start a comment. -/
def suspiciousUnaryAt? (src : Array Char) (n : BNode α) : Option (OpReport α) := do
  let .bin op := n.kind | none
  let #[_, b] := n.kids | none
  let .neg := b.kind | none
  let #[y] := b.kids | none
  let m := b.range.start
  let adjacent := m ≥ op.length && textOf src { start := m - op.length, stop := m } == op
  let spaced := src[m + 1]?.any Char.isWhitespace
  unless suspiciousUnaryOp (punctuatorOps.contains op) adjacent spaced do none
  let operand := textOf src { start := (withParensIn src b.range y.range).start, stop := n.range.stop }
  let neg := if operand.startsWith "-" then s!"- {operand}" else s!"-{operand}"
  let fixed := textOf src { start := n.range.start, stop := m } ++ " " ++ neg
  return { lint := .suspiciousUnaryOpFormatting, ref := n.ref, msg := suspiciousUnaryOpMsg op fixed }

/-- A value that `contradictory_comparisons` compares with: an integer, a
string or a `Bool` literal, or a variant without a payload, by its path. -/
inductive ConstOperand where
  | int (k : Int)
  | str (s : String)
  | bool (b : Bool)
  | variant (v : String)
  deriving Inhabited, BEq

/-- Whether `a` and `b`, neither an integer, are distinct values: two string
literals written differently, without escape sequences, two `Bool`
literals, or two variants. -/
def ConstOperand.distinct : ConstOperand → ConstOperand → Bool
  | .str s, .str t => s != t && !s.contains '\\' && !t.contains '\\'
  | .bool b, .bool c => b != c
  | .variant v, .variant w => v != w
  | _, _ => false

/-- The value that `n` is written as, if it is a literal or, by `variant?`,
a variant without a payload. -/
def constOperand? (src : Array Char) (variant? : α → Option String) (n : BNode α) : Option ConstOperand :=
  let t := textOf src n.range
  match n.kind, intLiteral? src n with
  | .lit b, _ => some (.bool b)
  | _, some k => some (.int k)
  | .atom, none =>
    if t.length ≥ 2 && t.startsWith "\"" && t.endsWith "\"" && t.toList.count '"' == 2 then some (.str t)
    else (variant? n.ref).map .variant
  | _, none => none

/-- The comparison `n` is, if one operand is a value that `constOperand?`
sees, the right one if both are: the other operand's text, the comparison
with that operand on the left, and the value. -/
def constComparison? (src : Array Char) (variant? : α → Option String) (n : BNode α) :
    Option (String × Comparison × ConstOperand) := do
  let .bin op := n.kind | none
  let c ← Comparison.ofOp? op
  let #[a, b] := n.kids | none
  match constOperand? src variant? b with
  | some k => return (textOf src a.range, c, k)
  | none => return (textOf src b.range, c.mirror, ← constOperand? src variant? a)

/-- `contradictory_comparisons` on `n`, an `and` or an `or`
(`lint::contradictory_comparisons`, `lint::contradictory_equalities`). -/
def contradictoryAt? (src : Array Char) (variant? : α → Option String) (n : BNode α) (conj : Bool) :
    Option (OpReport α) := do
  let #[l, r] := n.kids | none
  let (x1, c1, k1) ← constComparison? src variant? l
  let (x2, c2, k2) ← constComparison? src variant? r
  unless writtenSame x1 x2 do none
  let fires := match k1, k2 with
    | .int a, .int b => contradictoryComparisons conj c1 a c2 b
    | .int _, _ | _, .int _ => false
    | _, _ => contradictoryEqualities conj c1 c2 (k1.distinct k2)
  unless fires do none
  return { lint := .contradictoryComparisons, ref := n.ref, msg := contradictoryMsg conj }

/-- Whether `contradictory_comparisons` fires on `a OP₁ x OP₂ b` within a
chained comparison, where `a` and `b` are integers: on `x OP₁' a and x OP₂
b`, with `OP₁'` the mirror of `OP₁` (`lint::contradictory_chain`). -/
def contradictoryChain (c1 : Comparison) (a : Int) (c2 : Comparison) (b : Int) : Bool :=
  contradictoryComparisons true c1.mirror a c2 b

/-- `contradictory_comparisons` on `n`, a chained comparison of `ops`: at
each operand between two integer literals (`lint::contradictory_chain`). -/
def contradictoryChainAt? (src : Array Char) (n : BNode α) (ops : Array String) : Option (OpReport α) := do
  guard (n.kids.size == ops.size + 1)
  let fires := (List.range (ops.size - 1)).any fun i => Id.run do
    let (some c1, some c2) := (Comparison.ofOp? ops[i]!, Comparison.ofOp? ops[i + 1]!) | return false
    let (some a, some b) := (n.kids[i]?.bind (intLiteral? src ·), n.kids[i + 2]?.bind (intLiteral? src ·))
      | return false
    return contradictoryChain c1 a c2 b
  guard fires
  let msg := contradictoryMsg true
  return { lint := .contradictoryComparisons, ref := n.ref
           msg := { msg with notes := #["note: a bound may not be the one meant, or the chain may order the wrong way"] } }

/-- `redundant_comparisons` on `n`, an `and` or an `or`, in `slot` within
`parent` (`lint::redundant_comparisons`). Two comparisons written the same
are left to `eq_op`. -/
def redundantAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) (conj : Bool) :
    Option (OpReport α) := do
  let #[l, r] := n.kids | none
  let (x1, c1, .int a) ← constComparison? src (fun _ => none) l | none
  let (x2, c2, .int b) ← constComparison? src (fun _ => none) r | none
  unless writtenForm x1 == writtenForm x2 && !writtenSame (textOf src l.range) (textOf src r.range) do none
  let (true, keepFirst) := redundantComparisons conj c1 a c2 b | none
  let fixed := placed src n slot parent ((if keepFirst then l else r).text src)
  return { lint := .redundantComparisons, ref := n.ref, msg := redundantComparisonsMsg fixed }

/-- Why `overly_complex_bool_expr` drops an operand (`lint::BoolRule`). -/
inductive BoolRule where
  /-- `a or (a and b)` is `a`, and `a and (a or b)` is `a`. -/
  | absorption
  /-- `a and not a` is `false`. -/
  | contradiction
  /-- `a or not a` is `true`. -/
  | excludedMiddle
  deriving Inhabited, BEq, DecidableEq, Repr

/-- One layer of an expression, as `overly_complex_bool_expr` reads it: an
`and`, an `or`, a `not`, or another form. -/
inductive BoolLayer (α : Type) where
  | and (a b : α)
  | or (a b : α)
  | not (a : α)
  | other

/-- What the fix of `overly_complex_bool_expr` writes: the left operand,
the right one, or a `Bool` (`lint::Kept`). -/
inductive Kept where
  | left
  | right
  | constant
  deriving Inhabited, BEq, DecidableEq, Repr

section OverlyComplex
variable {α : Type} (layer : α → BoolLayer α) (same : α → α → Bool)

/-- `k` is `p or q`, in an `and` if `conj`, or `p and q`, in an `or`, where
`p` or `q` is the same as `o` (`lint::absorbs_operand?`). -/
def absorbsOperand (conj : Bool) (k o : α) : Bool :=
  match layer k with
  | .or p q => conj && (same p o || same q o)
  | .and p q => !conj && (same p o || same q o)
  | _ => false

/-- `k` is `not p`, where `p` is the same as `o` (`lint::negates_operand?`). -/
def negatesOperand (k o : α) : Bool :=
  match layer k with
  | .not p => same p o
  | _ => false

/-- Whether `overly_complex_bool_expr` fires on `e`, and by which rule, with
what its fix writes (`lint::overly_complex_bool_expr`). A negation where
`rewritten` holds, one that `nonminimal_bool` rewrites, does not make it
fire. Both front ends run it over their expressions, with `same` the test
of being written the same, which is trusted and checked by the ui tests;
`Impls/Rewrites.lean` proves that it meets the procedure over `lang::Expr`,
with `=`, and `rewritten` the procedure's `negation_rewritten?`. -/
def overlyComplexRule (rewritten : α → Bool) (e : α) : Option (BoolRule × Kept) :=
  let go (conj : Bool) (l r : α) : Option (BoolRule × Kept) :=
    if absorbsOperand layer same conj r l then some (.absorption, .left)
    else if absorbsOperand layer same conj l r then some (.absorption, .right)
    else
      let negation? := if negatesOperand layer same r l then some r
        else if negatesOperand layer same l r then some l else none
      match negation? with
      | some k => if rewritten k then none else some (if conj then .contradiction else .excludedMiddle, .constant)
      | none => none
  match layer e with
  | .and l r => go true l r
  | .or l r => go false l r
  | _ => none

end OverlyComplex

/-- `overly_complex_bool_expr` by `rule`, on an `and`, if `conj`, or an
`or`, whose fix is `fixed`. -/
def overlyComplexBoolMsg (conj : Bool) (rule : BoolRule) (fixed : String) (range? : Option Range := none) : Msg :=
  let op := if conj then "and" else "or"
  let (headline, label, note) := match rule with
    | .absorption => (s!"this `{op}` has an operand that does not change its value", "the other operand decides it",
      "note: `a or (a and b)` is `a`, and `a and (a or b)` is `a`")
    | .contradiction => ("this `and` is always `false`", "an operand and its negation",
      "note: one of the operands is probably not the one meant")
    | .excludedMiddle => ("this `or` is always `true`", "an operand and its negation",
      "note: one of the operands is probably not the one meant")
  { code? := some Lint.overlyComplexBoolExpr.code, headline, label? := some label, notes := #[note]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed, range? }] }

/-- An expression as `overly_complex_bool_expr` reads it. -/
def BNode.boolLayer (n : BNode α) : BoolLayer (BNode α) :=
  match n.kind, n.kids with
  | .bin "and", #[l, r] => .and l r
  | .bin "or", #[l, r] => .or l r
  | .not, #[a] => .not a
  | _, _ => .other

/-- `overly_complex_bool_expr` on `n`, an `and` if `conj`, or an `or`, in
`slot` within `parent` (`lint::overly_complex_bool_expr`). -/
def overlyComplexAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) (conj : Bool) :
    Option (OpReport α) := do
  let same (a b : BNode α) := writtenSame (textOf src a.range) (textOf src b.range)
  let rewritten (k : BNode α) := ((k.toEx 3).simplerForm .nonminimalBool).isSome
  let (rule, kept) ← overlyComplexRule BNode.boolLayer same rewritten n
  let #[l, r] := n.kids | none
  let t := match kept with
    | .left => l.text src
    | .right => r.text src
    | .constant => { text := toString (rule == .excludedMiddle), prec := BKind.atom.prec }
  -- An operand in parentheses: the fix replaces them too, and has the
  -- parentheses that its slot needs, rather than keeping those of `n`.
  match slot, parensAround? src parent n.range with
  | some _, some _ =>
    let outer := withParensIn src parent n.range
    let fixed := t.inSlot slot (followedAt src outer)
    return { lint := .overlyComplexBoolExpr, ref := n.ref, msg := overlyComplexBoolMsg conj rule fixed (some outer) }
  | _, _ =>
    let fixed := placed src n slot parent t
    return { lint := .overlyComplexBoolExpr, ref := n.ref, msg := overlyComplexBoolMsg conj rule fixed }

/-- `erasing_op` on `n`, a binary operator (`lint::erasing_op`). -/
def erasingOpAt? (src : Array Char) (n : BNode α) : Option (OpReport α) := do
  let .bin op := n.kind | none
  if op == "div" || op == "mod" then
    let #[a, _] := n.kids | none
    guard (erasingDivision (intLiteral? src a))
    return { lint := .erasingOp, ref := n.ref, msg := erasingDivisionMsg op }
  let o ← InfixOp.ofOp? op
  let #[a, b] := n.kids | none
  -- `erasingOp` reads `same` only for these operators.
  let same := (o matches .inter | .minus | .subset) && writtenSame (textOf src a.range) (textOf src b.range)
  unless erasingOp o (identityOperand src a) (identityOperand src b) same do none
  return { lint := .erasingOp, ref := n.ref, msg := erasingOpMsg o }

/-- Whether `precedence` fires on an operand of `outer` whose outermost
operator is `inner`, if it is not `parenthesized` (`lint::precedence`). -/
def precedenceFires (outer inner : InfixOp) (parenthesized : Bool) : Bool :=
  !parenthesized && ((outer == .or && inner == .and)
    || ((outer == .union || outer == .minus) && (inner == .inter || inner == .join)))

/-- An operand `t` of `outer`, whose outermost operator is `inner`,
written without the parentheses that its precedence implies. -/
def precedenceMsg (outer inner t : String) : Msg :=
  { code? := some Lint.precedence.code, headline := s!"`{inner}` is an operand of `{outer}` without parentheses"
    label? := some s!"binds more tightly than `{outer}`"
    notes := #[s!"note: `{inner}` binds more tightly than `{outer}`, so this is `({t})` already"]
    fixes := #[{ msg := "add the parentheses, which keep the meaning", replacement := s!"({t})" }] }

/-- `precedence` on the operands of `n`. -/
def precedenceAt (src : Array Char) (n : BNode α) : Array (OpReport α) :=
  match n.kind with
  | .bin op => match InfixOp.ofOp? op with
    | some o => n.kids.filterMap fun k => do
      let .bin iop := k.kind | none
      let i ← InfixOp.ofOp? iop
      unless precedenceFires o i (enclosed src n.range k.range) do none
      return { lint := .precedence, ref := k.ref, msg := precedenceMsg op iop (textOf src k.range) }
    | none => #[]
  | _ => #[]

/-- The tests of the chain of `else if` that starts at `n`, in order. -/
partial def ifTests (n : BNode α) : Array (BNode α) :=
  match n.kind, n.kids with
  | .ite, #[c, _, e] => #[c] ++ ifTests e
  | _, _ => #[]

/-- The position of the first test of a chain of `else if` before the
one at `i` that is written the same, given each test's written form
(`lint::ifs_same_cond`). -/
def earlierSame (forms : Array String) (i : Nat) : Option Nat :=
  (List.range i).find? fun j => forms[j]! == forms[i]!

/-- The first earlier scrutinee written the same, from their written
forms (`lint::duplicate_scrutinee`). All scrutinees of one match see the
same outer scope. The bound also makes the decision total for callers
asking about a position outside the scrutinees. -/
def duplicateScrutinee (forms : Array String) (i : Nat) : Option Nat :=
  if i < forms.size then earlierSame forms i else none

/-- Repeated columns, each with its first earlier column and, if there is
one, the first row whose patterns in those two columns cannot both match.
Both front ends supply only the texts without outer parentheses, types
and resolved patterns, as for `eq_op`'s operands.
The row note uses `Pat.overlapWit?` (`lang::pattern_overlap`); choosing its
first row is checked by the ui tests and CLI snapshots, not the `impl`
of `lint::duplicate_scrutinee`. -/
def duplicateScrutinees (texts : Array String) (sigs : Sigs) (types : Array PatTy)
    (rows : Array (Array Pat)) : Array (Nat × Nat × Option Nat) := Id.run do
  if texts.size < 2 then return #[]
  let forms := texts.map writtenForm
  let mut out := #[]
  for j in [:texts.size] do
    if let some i := duplicateScrutinee forms j then
      let row? := rows.toList.findIdx? fun ps =>
        match ps[i]?, ps[j]?, types[j]? with
        | some p, some q, some ty => (p.overlapWit? sigs ty q).isNone
        | _, _, _ => false
      out := out.push (j, i, row?)
  return out

def duplicateScrutineeMsg (first : Nat) (row? : Option Nat) : Msg :=
  { code? := some Lint.duplicateScrutinee.code
    headline := s!"this scrutinee is written the same as scrutinee {first + 1}"
    label? := some s!"repeats scrutinee {first + 1}"
    notes := #["note: these columns always have the same value; rows requiring different values cannot be taken"]
      ++ row?.toArray.map (fun r => s!"note: row {r + 1} cannot be taken because its patterns in these columns are disjoint") }

/-- `ifs_same_cond` on the chain of `else if` that starts at `n`
(`lint::ifs_same_cond`): at each test written the same as an earlier
one, naming the first. -/
def ifsSameCondAt (src : Array Char) (n : BNode α) : Array (OpReport α) :=
  let tests := ifTests n
  let texts := tests.map fun t => textOf src t.range
  let forms := texts.map writtenForm
  tests.zipIdx.filterMap fun (t, i) => do
    let earlier := (earlierSame forms i).map (texts[·]!)
    unless ifsSameCond earlier.isSome do none
    return { lint := .ifsSameCond, ref := t.ref, msg := ifsSameCondMsg (earlier.getD "") }

/-- Whether `chainable_comparison` joins the conjuncts `l and r`, and
whether its fix writes `l`, and `r`, the other way round
(`lint::chainable_comparison`): from whether each orders ascending, with
`<` and `<=`, whether each is one comparison, and which of their first and
last operands are written the same. -/
def chainableComparison (lAsc rAsc lSingle rSingle lastFirst firstLast firstFirst lastLast : Bool) :
    Bool × Bool × Bool :=
  let keep := lAsc == rAsc && lastFirst && !firstLast
  let flipLeft := lSingle && lAsc != rAsc && firstFirst && !lastLast
  let flipRight := rSingle && lAsc != rAsc && lastLast && !firstFirst
  let flipBoth := lSingle && rSingle && lAsc == rAsc && firstLast && !lastFirst
  (keep || flipLeft || flipRight || flipBoth, flipLeft || flipBoth, flipRight || flipBoth)

/-- `chainable_comparison`'s message, whose fix is `fixed`, or none but a
note if a comment between the comparisons would be lost (`commented`). -/
def chainableComparisonMsg (fixed : String) (commented : Bool) : Msg :=
  { code? := some Lint.chainableComparison.code, headline := "these comparisons can be chained"
    label? := some "comparisons that share an operand"
    notes := if commented then #[s!"help: write `{fixed}`",
      "note: `fren fix` leaves this, since the chain would lose the comment between the comparisons"] else #[]
    fixes := if commented then #[] else #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- A conjunct that `chainable_comparison` can join (`lint::Chain`): a
comparison that orders, or a chained comparison, as its operands and
operators. -/
structure ChainPart (σ : Type) where
  operands : Array σ
  ops : Array String

/-- Whether `op` orders ascending: `<` or `<=`. -/
def ascendingOp (op : String) : Bool := op matches "<" | "<="

/-- Whether `op` orders descending: `>` or `>=`. -/
def descendingOp (op : String) : Bool := op matches ">" | ">="

def ChainPart.ascending (p : ChainPart σ) : Bool := p.ops.all ascendingOp

/-- The conjunct, written the other way round: `a < b` as `b > a`. -/
def ChainPart.flip (p : ChainPart σ) : ChainPart σ :=
  { operands := p.operands.reverse
    ops := p.ops.reverse.map fun op => ((Comparison.ofOp? op).map (·.mirror.op)).getD op }

/-- The conjunct with each operand `f` of it: as written, for `f` the
operand's written form. -/
def ChainPart.map (f : σ → τ) (p : ChainPart σ) : ChainPart τ := { operands := p.operands.map f, ops := p.ops }

/-- Whether `chainable_comparison` joins the conjuncts `l and r`, and
whether its fix writes `l`, and `r`, the other way round
(`lint::chainable_comparison`), each operand as written:
`chainableComparison` of what their operands and operators are. -/
def chainFlips (l r : ChainPart String) : Bool × Bool × Bool :=
  chainableComparison l.ascending r.ascending (l.ops.size == 1) (r.ops.size == 1)
    (l.operands.back! == r.operands[0]!) (l.operands[0]! == r.operands.back!)
    (l.operands[0]! == r.operands[0]!) (l.operands.back! == r.operands.back!)

/-- The chained comparison that `chainable_comparison`'s fix writes for
`l and r`, where `fl` and `fr` say which it writes the other way round
(`lint::chainable_joined`): `l`'s operands, then `r`'s after its first,
which is `l`'s last. -/
def ChainPart.join (l r : ChainPart σ) (fl fr : Bool) : ChainPart σ :=
  let l := if fl then l.flip else l
  let r := if fr then r.flip else r
  { operands := l.operands ++ r.operands.extract 1, ops := l.ops ++ r.ops }

/-- Whether `ops` are the operators of a chain that orders one way: one or
more, each `<` or `<=`, or each `>` or `>=`. -/
def orderingOps (ops : Array String) : Bool :=
  !ops.isEmpty && (ops.all ascendingOp || ops.all descendingOp)

/-- `n` as a conjunct that `chainable_comparison` can join, if it is one:
a comparison that orders, or a chained comparison that orders one way,
which is the one kind that is not an error. -/
def chainPart? (n : BNode α) : Option (ChainPart (BNode α)) :=
  match n.kind with
  | .bin op => if orderingOps #[op] && n.kids.size == 2 then some ⟨n.kids, #[op]⟩ else none
  | .chain ops => if orderingOps ops && ops.size + 1 == n.kids.size then some ⟨n.kids, ops⟩ else none
  | _ => none

/-- The text of the chained comparison of `operands` and `ops`, each
operand in parentheses where it needs them, where `followed` says whether
an operator follows it. -/
def chainText (src : Array Char) (operands : Array (BNode α)) (ops : Array String) (followed : Bool) : BText :=
  let slots := (BKind.chain ops).slots
  let texts := operands.mapIdx fun i k => (k.text src).inSlot (slots[i]?.join) (i + 1 < operands.size || followed)
  let rest := (ops.zip (texts.extract 1)).foldl (fun acc (op, t) => s!"{acc} {op} {t}") (texts[0]?.getD "")
  { text := rest, prec := (BKind.chain ops).prec }

/-- `chainable_comparison` on `n`, an `and` in `slot` within `parent`, if
it is the top of a run of `and` (`lint::chainable_comparison`): one
report for each run of adjacent conjuncts that chain, from the first to
the last, which are not in parentheses. -/
def chainableAt [Inhabited α] (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Array (OpReport α) := Id.run do
  let inRun := slot.any (fun s => s.outer == (BKind.bin "and").prec && !s.right) && !enclosed src parent n.range
  if n.kind != .bin "and" || inRun then return #[]
  let cs := conjuncts src n
  let form (k : BNode α) := writtenForm (textOf src k.range)
  let bare (k : BNode α) := !enclosed src n.range k.range
  let mut out := #[]
  -- The run so far: its first conjunct, the chain, and how many it joins.
  let mut run : Option (Nat × ChainPart (BNode α) × Nat) := none
  for i in [0:cs.size] do
    let k := cs[i]!
    let next? := if bare k then chainPart? k else none
    let joined? := do
      let (start, l, m) ← run
      let r ← next?
      let (fires, fl, fr) := chainFlips (l.map form) (r.map form)
      guard fires
      pure (start, l.join r fl fr, m + 1)
    match joined? with
    | some j => run := some j
    | none =>
      if let some (start, c, m) := run then if m ≥ 2 then out := out.push (start, i - 1, c)
      run := next?.map (i, ·, 1)
  if let some (start, c, m) := run then if m ≥ 2 then out := out.push (start, cs.size - 1, c)
  return out.map fun (a, b, c) =>
    let whole := a == 0 && b + 1 == cs.size
    let range : Range := { start := cs[a]!.range.start, stop := cs[b]!.range.stop }
    let t := chainText src c.operands c.ops (followedAt src range)
    let fixed := if whole then placed src n slot parent t else t.text
    let commented := (withoutComments (textOf src range)).length != (textOf src range).length
    { lint := .chainableComparison, ref := cs[a]!.ref, last? := some cs[b]!.ref, msg := chainableComparisonMsg fixed commented }

end Fren.Core
