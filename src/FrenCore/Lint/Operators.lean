-- keep-sorted start
import FrenCore.Lint.Collections
import FrenCore.Lint.Expressions
-- keep-sorted end

/-!
# Operator rules and expression node helpers

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Operators and methods -/

/-- Whether `a OP b` holds, from how `a` compares with `b`
(`lint::comparison_holds`). -/
def Comparison.holds : Comparison → Ordering → Bool
  | .eq, o => o == .eq
  | .ne, o => o != .eq
  | .lt, o => o == .lt
  | .le, o => o != .gt
  | .gt, o => o == .gt
  | .ge, o => o != .lt

/-- The comparison that `a OP₁ b and a OP₂ b`, or with `or` if not `conj`,
is, if one is and it is neither of the two (`lint::double_comparison`). -/
def doubleComparison (conj : Bool) (first second : Comparison) : Option Comparison :=
  let both (o : Ordering) := if conj then first.holds o && second.holds o else first.holds o || second.holds o
  Comparison.all.find? fun c => c != first && c != second && [Ordering.lt, .eq, .gt].all fun o => c.holds o == both o

/-- `a OP₁ b and a OP₂ b`, or `or`, as the text of the comparison it is. -/
def doubleComparisonMsg (fixed : String) : Msg :=
  { code? := some Lint.doubleComparison.code, headline := s!"these two comparisons are `{fixed}`"
    label? := some "compares the same operands twice"
    fixes := #[{ msg := "write it as one comparison", replacement := fixed }] }

/-- Whether `x OP k` bounds `x` from below (`lint::disjoint`). -/
def Comparison.boundsBelow (c : Comparison) : Bool := c matches .eq | .gt | .ge

/-- Whether `x OP k` bounds `x` from above (`lint::disjoint`). -/
def Comparison.boundsAbove (c : Comparison) : Bool := c matches .eq | .lt | .le

/-- The least integer `x` with `x OP k`, if `OP` bounds it from below. -/
def Comparison.least (c : Comparison) (k : Int) : Int := if c matches .gt then k + 1 else k

/-- The greatest integer `x` with `x OP k`, if `OP` bounds it from above. -/
def Comparison.greatest (c : Comparison) (k : Int) : Int := if c matches .lt then k - 1 else k

/-- Whether no integer `x` has both `x OP₁ a` and `x OP₂ b`
(`lint::disjoint`). -/
def disjointBounds (c1 : Comparison) (a : Int) (c2 : Comparison) (b : Int) : Bool :=
  (c1.boundsBelow && c2.boundsAbove && c1.least a > c2.greatest b)
    || (c2.boundsBelow && c1.boundsAbove && c2.least b > c1.greatest a)
    || (a == b && ((c1, c2) matches (.eq, .ne) | (.ne, .eq)))

/-- Whether `contradictory_comparisons` fires on `x OP₁ a and x OP₂ b`, or
`or` if not `conj`, of integers (`lint::contradictory_comparisons`): under
`and`, no `x` has both; under `or`, none has neither. -/
def contradictoryComparisons (conj : Bool) (c1 : Comparison) (a : Int) (c2 : Comparison) (b : Int) : Bool :=
  if conj then disjointBounds c1 a c2 b else disjointBounds c1.complement a c2.complement b

/-- Whether `contradictory_comparisons` fires on `x OP₁ a and x OP₂ b`, or
`or` if not `conj`, where `a` and `b` are not integers, from whether they
are distinct (`lint::contradictory_equalities`). -/
def contradictoryEqualities (conj : Bool) (c1 c2 : Comparison) (distinct : Bool) : Bool :=
  distinct && if conj then (c1, c2) matches (.eq, .eq) else (c1, c2) matches (.ne, .ne)

/-- `x OP₁ a and x OP₂ b`, or `or` if not `conj`, that is always `false`,
or `true`. -/
def contradictoryMsg (conj : Bool) : Msg :=
  { code? := some Lint.contradictoryComparisons.code
    headline := if conj then "these two comparisons cannot both hold" else "one of these two comparisons always holds"
    label? := some s!"always `{!conj}`"
    notes := #["note: `and` and `or` may be swapped, or a value may not be the one meant"] }

/-- Whether `redundant_comparisons` fires on `x OP₁ a and x OP₂ b`, or `or`
if not `conj`, of integers, and whether the fix keeps the first comparison,
rather than the second (`lint::redundant_comparisons`): under `and` the one
that implies the other, under `or` the one that the other implies. -/
def redundantComparisons (conj : Bool) (c1 : Comparison) (a : Int) (c2 : Comparison) (b : Int) : Bool × Bool :=
  let firstImplies := disjointBounds c1 a c2.complement b
  let secondImplies := disjointBounds c2 b c1.complement a
  (firstImplies || secondImplies, if conj then firstImplies else secondImplies)

/-- `x OP₁ a and x OP₂ b`, or `or`, as the text of the comparison kept. -/
def redundantComparisonsMsg (fixed : String) : Msg :=
  { code? := some Lint.redundantComparisons.code, headline := s!"these two comparisons are `{fixed}`"
    label? := some "one comparison implies the other"
    fixes := #[{ msg := "remove the comparison that adds nothing", replacement := fixed }] }

/-- Whether `bool_equality` fires on `a OP b` (`lint::bool_equality`). -/
def boolEquality (op : Comparison) (bools literal : Bool) : Bool := op == .eq && bools && !literal

/-- `a = b` on `Bool`s, as the text of `a iff b`. -/
def boolEqualityMsg (fixed : String) : Msg :=
  { code? := some Lint.boolEquality.code, headline := "equality of `Bool`s is `iff`"
    label? := some "compares two `Bool`s"
    notes := #["note: on `Bool`s, `=` and `iff` agree, and `iff` says that this is an equivalence"]
    fixes := #[{ msg := "write it with `iff`", replacement := fixed }] }

/-- What `s.index_of(t, 0) OP bound` says (`lint::IndexTest`). -/
inductive IndexTest where
  | found
  | absent
  | atStart
  | other
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What `s.index_of(t, 0) OP bound` says, with the call on the left
(`lint::index_test`). -/
def indexTest (op : Comparison) (bound : Int) : IndexTest :=
  match op with
  | .ge => if bound == 0 then .found else .other
  | .gt | .ne => if bound == -1 then .found else .other
  | .lt => if bound == 0 then .absent else .other
  | .le => if bound == -1 then .absent else .other
  | .eq => if bound == -1 then .absent else if bound == 0 then .atStart else .other

/-- A search written with `index_of`, `slice` or `at`, as the text of the
call of `method` that it is. -/
def manualMethodMsg (method fixed label : String) : Msg :=
  { code? := some Lint.manualMethod.code, headline := s!"this is a call of `{method}`", label? := some label
    fixes := #[{ msg := s!"call `{method}`", replacement := fixed }] }

/-- `s.at(0) = ""`, or `!=`, as the text of the collection compared with
`empty`, `""` or `[]` (`lint::first_empty`). -/
def firstEmptyMsg (fixed empty : String) : Msg :=
  { code? := some Lint.lengthZero.code, headline := s!"say whether it is empty with `{empty}`, not `at`"
    label? := some s!"compares the first {if empty == "[]" then "element" else "character"} with `{empty}`"
    fixes := #[{ msg := s!"compare with `{empty}`", replacement := fixed }] }

/-- `s.slice(0, s.len)`, as the text of `s`. -/
def redundantSlicingMsg (fixed : String) : Msg :=
  { code? := some Lint.redundantSlicing.code, headline := "this slice is the whole of its receiver"
    label? := some "from the start, as long as the receiver"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `s.replace(a, a)`, or `replace_all`, as the text of `s`. -/
def noEffectReplaceMsg (method fixed : String) : Msg :=
  { code? := some Lint.noEffectReplace.code, headline := s!"this `{method}` has no effect"
    label? := some "replaces with what it replaces"
    notes := #["note: the two arguments are written the same"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `a OP b` on integers. -/
def Comparison.compares : Comparison → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .gt, a, b => a > b
  | .ge, a, b => a ≥ b

/-- Whether `const_is_empty` fires on a comparison of the length of a
literal of `n` characters or elements with `bound`, `n OP bound` if
`lengthLeft` and `bound OP n` otherwise, where `set` says that it is a set's
or relation's, whose `card` may be fewer; and what the comparison always is
(`lint::const_is_empty`). -/
def constIsEmpty (op : Comparison) (bound : Int) (lengthLeft set : Bool) (n : Nat) : Bool × Bool :=
  let (emptiness, empty) := lengthZero op bound lengthLeft
  (!set || emptiness,
    if set then empty == (n == 0) else if lengthLeft then op.compares n bound else op.compares bound n)

/-- Whether `const_is_empty` fires on `a = E` or `a != E`, where `E` is
empty and `a` a literal of `n` characters or elements, and what it always
is (`lint::const_empty_equation`). -/
def constEmptyEquation (equal : Bool) (n : Nat) : Bool × Bool := (n > 0, equal == (n == 0))

/-- A test of a literal that is always `value`. -/
def constIsEmptyMsg (value : Bool) : Msg :=
  { code? := some Lint.constIsEmpty.code, headline := s!"this test of a literal is always `{value}`"
    label? := some "the literal's length is fixed"
    notes := #["note: the literal is probably not the one meant"] }

/-- Whether `else_extends` fires on a conditional that is an operand of an
operator of precedence `outer`, from the precedence `inner` of its `else`
branch (`lint::else_extends`). -/
def elseExtends (outer inner : Nat) (assoc : Assoc) (right : Bool) : Bool := !bareOperand outer inner assoc right

/-- A conditional that is an operand of `op`, as the text of its `else`
branch, and of the conditional with the branch in parentheses. -/
def elseExtendsMsg (op branch fixed : String) : Msg :=
  { code? := some Lint.elseExtends.code, headline := "the `else` branch extends past the operator"
    label? := some s!"the `else` branch is `{branch}`"
    notes := #[s!"note: the conditional is an operand of `{op}`, but its `else` branch extends as far right as possible"]
    fixes := #[{ msg := "put the `else` branch in parentheses, which keeps the meaning", replacement := fixed }] }

/-- An operator that `identity_op` looks at (`lint::IdentityOperator`). -/
inductive IdentityOperator where
  | add
  | sub
  | mul
  | concat
  | union
  | minus
  | div
  deriving Inhabited, BEq, DecidableEq, Repr

def IdentityOperator.ofOp? : String → Option IdentityOperator
  | "+" => some .add
  | "-" => some .sub
  | "*" => some .mul
  | "div" => some .div
  | "++" => some .concat
  | "union" => some .union
  | "minus" => some .minus
  | _ => none

/-- An operand, as `identity_op` sees it (`lint::IdentityOperand`):
`empty` is `""`, `[]` or `{}`. -/
inductive IdentityOperand where
  | zero
  | one
  | empty
  | negation
  | other
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What `identity_op` writes for `a OP b` (`lint::Rewrite`): `flip` is
`a - y` for `a + -y`, and `a + y` for `a - -y`. -/
inductive Rewrite where
  | keepLeft
  | keepRight
  | flip
  | unchanged
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What `identity_op` writes for `a OP b` (`lint::identity_op`). -/
def identityRewrite (op : IdentityOperator) (left right : IdentityOperand) : Rewrite :=
  match op with
  | .add => if right == .zero then .keepLeft else if left == .zero then .keepRight
    else if right == .negation then .flip else .unchanged
  | .sub => if right == .zero then .keepLeft else if right == .negation then .flip else .unchanged
  | .mul => if right == .one then .keepLeft else if left == .one then .keepRight else .unchanged
  | .div => if right == .one then .keepLeft else .unchanged
  | .concat | .union => if right == .empty then .keepLeft else if left == .empty then .keepRight else .unchanged
  | .minus => if right == .empty then .keepLeft else .unchanged

def identityOpMsg (fixed : String) (flip : Bool) : Msg :=
  { code? := some Lint.identityOp.code
    headline := if flip then "this negation can be the other operator" else "this operation has no effect"
    label? := some (if flip then "an operand that is a negation" else "leaves its other operand as it is")
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `erasing_op` fires on `a OP b`, where `same` says that `a` and
`b` are written the same, which `eq_op` reports for `inter` and `minus`
(`lint::erasing_op`). -/
def erasingOp (op : InfixOp) (left right : IdentityOperand) (same : Bool) : Bool :=
  match op, same with
  | .inter, true | .minus, true | .subset, true => false
  | .mul, _ => (left matches .zero) || (right matches .zero)
  | .inter, _ | .join, _ => (left matches .empty) || (right matches .empty)
  | .minus, _ | .subset, _ => (left matches .empty)
  | .in, _ => (right matches .empty)
  | _, _ => false

/-- Whether `erasing_op` fires on `a div k` or `a mod k`, from the value of
`a` if it is an integer literal, possibly negated (`lint::erasing_division`). -/
def erasingDivision (dividend : Option Int) : Bool := dividend == some 0

/-- `0 div k` or `0 mod k`, for `op`, `div` or `mod`. -/
def erasingDivisionMsg (op : String) : Msg :=
  { code? := some Lint.erasingOp.code, headline := s!"this `{op}` is always `0`", label? := some "divides `0`"
    notes := #["note: the dividend is probably not the one meant"] }

/-- The value that `a OP b` always has where `erasing_op` fires. -/
def erasingOpValue : InfixOp → String
  | .mul => "0"
  | .in => "false"
  | .subset => "true"
  | _ => "{}"

def erasingOpMsg (op : InfixOp) : Msg :=
  { code? := some Lint.erasingOp.code, headline := s!"this `{op.op}` is always `{erasingOpValue op}`"
    label? := some "ignores its other operand"
    notes := #["note: the literal is probably not the operand meant"] }

/-- Whether `ifs_same_cond` fires on a test of a chain of `else if`, from
whether an earlier test of the chain is written the same
(`lint::ifs_same_cond`). -/
def ifsSameCond (earlier : Bool) : Bool := earlier

/-- A test of a chain of `else if`, written the same as the earlier
`test`. -/
def ifsSameCondMsg (test : String) : Msg :=
  { code? := some Lint.ifsSameCond.code, headline := s!"`{test}` is already tested earlier in this chain"
    label? := some "the same as an earlier test"
    notes := #[s!"note: this branch is never taken: wherever `{test}` holds, the earlier branch is taken",
      "note: one of the tests is probably not the one meant"] }

/-- A message of an operator or method lint, whose first fix replaces the
text at `ref`, or from `ref` to `last?`, which ends it. -/
structure OpReport (α : Type) where
  lint : Lint
  ref : α
  msg : Msg
  last? : Option α := none
  /-- `fren fix` leaves this fix where it fixes this lint at this
  expression, whose fix overlaps it. -/
  unless? : Option (Lint × α) := none
  deriving Inhabited

/-- `r` with the parentheses around it within `outer`, however many. -/
partial def withParensIn (src : Array Char) (outer r : Range) : Range :=
  match parensAround? src outer r with
  | some r' => withParensIn src outer r'
  | none => r

/-- The operand `k` of an expression at `outer`, as written: with its
parentheses. -/
def operandText (src : Array Char) (outer : Range) (k : BNode α) : String := textOf src (withParensIn src outer k.range)

/-- `k`, without the parentheses around it, and its precedence. -/
def BNode.text (src : Array Char) (k : BNode α) : BText := { text := textOf src k.range, prec := k.kind.prec }

/-- `left OP right`, for a binary operator `op`, each operand in
parentheses if it needs them there. -/
def binText (op : String) (left right : BText) : BText :=
  let k := BKind.bin op
  { text := s!"{left.inSlot (some ⟨k.prec, k.assoc, false⟩)} {op} {right.inSlot (some ⟨k.prec, k.assoc, true⟩)}"
    prec := k.prec }

/-- A comparison of a length with `bound`, where `recv` is the collection,
without the parentheses around it, and `empty` the text of an empty one,
such as `""`, `[]` or `{}`. The fix puts `recv` in parentheses where it
needs them, as the left operand of `=` or `!=`. -/
def lengthZeroMsg (card : Bool) (recv : BText) (empty : String) (isEmpty : Bool) (bound : Int) : Msg :=
  let m := if card then "card" else "len"
  let fixed := (binText (if isEmpty then "=" else "!=") recv { text := empty, prec := BKind.atom.prec }).text
  { code? := some (if card then "F0716" else "F0715"), headline := s!"say whether it is empty with `{empty}`, not `{m}`"
    label? := some s!"compares a length with {bound}"
    fixes := #[{ msg := s!"compare with `{empty}`", replacement := fixed }] }

/-- The words that start an expression or a path, which a bound name
cannot be, though they are not reserved. -/
def expressionWords : List String := ["when", "unless", "not", "true", "false", "self", "super"]

/-- Whether `n` is directly in parentheses of its own within `parent`:
the parentheses of an application, written right after its name, are not
around its argument alone. -/
def inOwnParens (src : Array Char) (n : BNode α) (parent : Range) : Bool :=
  let call (r : Range) : Bool := Id.run do
    let mut i := r.start
    while i > 0 && isWordChar src[i - 1]! do i := i - 1
    let w := textOf src { start := i, stop := r.start }
    return !w.isEmpty && !reservedWords.contains w && !expressionWords.contains w
  (parensAround? src parent n.range).any (!call ·)

/-- The text of `t`, which replaces `n`, in `slot` within `parent`: in
parentheses if it needs them there and `n` is not already in them. -/
def placed (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) (t : BText) : String :=
  if enclosed src parent n.range then t.text else t.inSlot slot (followedAt src n.range)

/-- The comparison `n` is, with its operands' texts as `writtenForm` gives them. -/
def comparisonOf? (src : Array Char) (n : BNode α) : Option (Comparison × String × String) := do
  let .bin op := n.kind | none
  let #[a, b] := n.kids | none
  let c ← Comparison.ofOp? op
  return (c, writtenForm (textOf src a.range), writtenForm (textOf src b.range))

/-- The integer that `n` is written as, if it is a literal or a negated one. -/
def intLiteral? (src : Array Char) (n : BNode α) : Option Int :=
  match n.kind with
  | .atom | .neg => (writtenForm (textOf src n.range)).toInt?
  | _ => none

/-- Whether `k` is written `e.len` or `(e).len`, where `o` is the text of
`e` without whitespace. -/
def isLenOf (src : Array Char) (o : String) (k : BNode α) : Bool :=
  let t := writtenForm (textOf src k.range)
  t == o ++ ".len" || t == s!"({o}).len"

/-- Whether `k` is a literal of one character, or a sequence literal of one
element. -/
def oneElement (src : Array Char) (k : BNode α) : Bool :=
  let t := textOf src k.range
  ((Lean.Syntax.decodeStrLit t).any (·.length == 1)) ||
    (k.kind == .atom && t.startsWith "[" && t.endsWith "]" && k.kids.size == 1)

/-- Whether `k`, the first operand of `n`, an atom, is its receiver: `n`
reads a field of it, or indexes it. -/
def isReceiverOf (src : Array Char) (n k : BNode α) : Bool := Id.run do
  let r := withParensIn src n.range k.range
  let mut i := r.stop
  while i < n.range.stop && src[i]!.isWhitespace do i := i + 1
  return r.start == n.range.start && (src[i]? == some '.' || src[i]? == some '[')

/-- The conjuncts of the run of `and` that `n` is the top of, in order:
through each left operand that is an `and` not in parentheses. -/
partial def conjuncts (src : Array Char) (n : BNode α) : Array (BNode α) :=
  match n.kind, n.kids with
  | .bin "and", #[l, r] =>
    (if l.kind == .bin "and" && !enclosed src n.range l.range then conjuncts src l else #[l]).push r
  | _, _ => #[n]

end Fren.Core
