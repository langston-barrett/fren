-- keep-sorted start
import FrenCore.Lint.Operators
-- keep-sorted end

/-!
# Integer and ordering lints

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Integers -/

/-- Whether a comparison of `x` on its left says that `x` is below the
other operand, or above it: `<` and `<=`, or `>` and `>=`. -/
def Comparison.below : Comparison → Bool
  | .lt | .le => true
  | _ => false

def Comparison.above : Comparison → Bool
  | .gt | .ge => true
  | _ => false

/-- The type that an ordering compares, as the lints of integers see it
(`lint::Ordered`): `Int` or `Nat`, an ordered enumeration, or another,
such as `String` or a newtype. -/
inductive Ordered where
  | number
  | enumeration
  | other
  deriving Inhabited, DecidableEq, Repr

/-- Whether `manual_abs` fires on `if x OP 0 then a else b`, where `op` has
`x` on its left, mirrored where `x` is written on the right, and
`negatedThen` says that `a` is `-x` and `b` is `x`, rather than the reverse
(`lint::manual_abs`). -/
def manualAbs (compared : Ordered) (op : Comparison) (negatedThen : Bool) : Bool :=
  compared == .number && ((op.below && negatedThen) || (op.above && !negatedThen))

def manualAbsMsg (fixed : String) : Msg :=
  { code? := some Lint.manualAbs.code, headline := "this conditional is the absolute value"
    label? := some "negates a negative operand"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `manual_abs_diff` fires on `if a OP b then c else d`, where
`thenLeftFirst` says that `c` is `a - b` and `d` is `b - a`, rather than
the reverse (`lint::manual_abs_diff`). -/
def manualAbsDiff (op : Comparison) (thenLeftFirst : Bool) : Bool :=
  (op.above && thenLeftFirst) || (op.below && !thenLeftFirst)

/-- Whether `manual_abs_diff` fires on `if a OP b then c else d`, where
`compared` is the type that `OP` compares, `a` and `b` are the written
forms of its operands, and `c` and `d` those of the operands of the
branches, each a subtraction (`lint::manual_abs_diff`). -/
def manualAbsDiffRule (op : Comparison) (compared : Ordered) (a b : String) (c d : String × String) : Bool :=
  compared == .number && a != b
    && ((c == (a, b) && d == (b, a) && manualAbsDiff op true) || (c == (b, a) && d == (a, b) && manualAbsDiff op false))

def manualAbsDiffMsg (fixed : String) : Msg :=
  { code? := some Lint.manualAbsDiff.code, headline := "this conditional is the absolute value of a difference"
    label? := some "subtracts the lesser operand from the greater"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- `min` or `max` (`lint::MinMax`). -/
inductive MinMax where
  | min
  | max
  deriving Inhabited, BEq, DecidableEq, Repr

def MinMax.name : MinMax → String
  | .min => "min"
  | .max => "max"

def MinMax.ofName? : String → Option MinMax
  | "min" => some .min
  | "max" => some .max
  | _ => none

/-- The method that `if a OP b then c else d` is, where `thenLeft` says
that `c` is `a` and `d` is `b`, rather than the reverse, if
`manual_min_max` fires (`lint::manual_min_max`). -/
def manualMinMax (op : Comparison) (thenLeft : Bool) : Option MinMax :=
  if op.below then some (if thenLeft then .min else .max)
  else if op.above then some (if thenLeft then .max else .min)
  else none

/-- The method that `if a OP b then c else d` is, and whether the fix's
receiver is `a`, rather than `b`, if `manual_min_max` fires, where
`compared` is the type that `OP` compares, `a`, `b`, `c` and `d` are
written forms, and `aLit` and `bLit` say whether `a` and `b` have an
integer literal in them (`lint::manual_min_max`). -/
def manualMinMaxRule (op : Comparison) (compared : Ordered) (a b c d : String) (aLit bLit : Bool) :
    Option (MinMax × Bool) :=
  if compared != .other && a != b && !(aLit && bLit) && ((c == a && d == b) || (c == b && d == a)) then
    (manualMinMax op (c == a)).map (·, !aLit)
  else none

def manualMinMaxMsg (m : MinMax) (fixed : String) : Msg :=
  { code? := some Lint.manualMinMax.code, headline := s!"this conditional is `{m.name}`"
    label? := some s!"gives the {if m == .min then "lesser" else "greater"} operand"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `manual_clamp` fires on `if x OP₁ b₁ then b₁ else if x OP₂ b₂
then b₂ else x`, where each comparison has `x` on its left and the bounds
are integer literals (`lint::manual_clamp`). -/
def manualClamp (compared : Ordered) (firstOp secondOp : Comparison) (first second : Int) : Bool :=
  compared == .number && ((firstOp.below && secondOp.above && first ≤ second) || (firstOp.above && secondOp.below && second ≤ first))

def manualClampMsg (fixed : String) : Msg :=
  { code? := some Lint.manualClamp.code, headline := "this conditional keeps its operand between two bounds"
    label? := some "gives a bound where the operand is past it"
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- An operand of the `+` in `(p + q) mod k`, as `manual_rem_euclid` sees
it (`lint::Summand`): its written form, and the written form of its
divisor if it is a `mod`. -/
structure Summand where
  text : String
  divisor? : Option String
  deriving Inhabited, BEq, Repr

/-- Whether `manual_rem_euclid` fires on `(p + q) mod k`, where `divisor`
is the written form of `k` (`lint::manual_rem_euclid`): the first of `p`
and `q` that is a `mod` is by `k`, and the other is written as `k`. -/
def manualRemEuclidRule (p q : Summand) (divisor : String) : Bool :=
  match p.divisor?, q.divisor? with
  | some d, _ => d == divisor && q.text == divisor
  | none, some d => d == divisor && p.text == divisor
  | none, none => false

def manualRemEuclidMsg (fixed : String) : Msg :=
  { code? := some Lint.manualRemEuclid.code, headline := "`mod` is never negative already"
    label? := some "adds the divisor to a remainder"
    notes := #["note: `mod` is Euclidean, so `a mod k` is at least 0 and below the size of `k`, even where `a` is negative"]
    fixes := #[{ msg := s!"write `{fixed}`", replacement := fixed }] }

/-- Whether `modulo_one` fires on `x mod k`, from the value of `k` if it
is an integer literal, possibly negated (`lint::modulo_one`). -/
def moduloOne (divisor : Option Int) : Bool := divisor == some 1 || divisor == some (-1)

def moduloOneMsg (k : String) : Msg :=
  { code? := some Lint.moduloOne.code, headline := s!"the remainder by `{k}` is always `0`", label? := some "always `0`"
    notes := #["note: the divisor is probably not the one meant"] }

/-- Whether `min_max` fires on `x.inner(a).outer(b)`, where `a` and `b`
are integer literals (`lint::min_max`). -/
def minMax (inner outer : MinMax) (a b : Int) : Bool :=
  match inner, outer with
  | .min, .max => a < b
  | .max, .min => a > b
  | _, _ => false

def minMaxMsg (inner outer : MinMax) (b : String) : Msg :=
  { code? := some Lint.minMax.code, headline := s!"this `{inner.name}` and `{outer.name}` always give `{b}`"
    label? := some s!"always `{b}`"
    notes := #["note: the bounds are probably swapped"] }

/-- Whether `eq_op` fires on a call of `min` or `max`, from whether its
receiver and argument are written the same (`lint::eq_op_method`). -/
def eqOpMethod (receiver argument : String) : Bool := receiver == argument

/-- `r.m(r)`, for `min` or `max`, where `r` is the text of the receiver
(`lint::eq_op_method`). -/
def eqOpMethodMsg (m : MinMax) (r : String) : Msg :=
  { code? := some Lint.eqOp.code, headline := s!"the receiver and the argument of `{m.name}` are written the same"
    label? := some s!"the same as `{r}`"
    notes := #["note: one of them is probably not the operand meant"] }

/-- Whether the text `t` has an integer literal in it: a digit that does
not continue a name. Such a literal is a `Nat` or an `Int` by where it is
(`Reqs/Lang/Expressions#natural-numbers`), so an operand with one can
change type when it moves. -/
def hasIntLiteral (t : String) : Bool := Id.run do
  let cs := (withoutComments t).toList.toArray
  for i in [0:cs.size] do
    if cs[i]!.isDigit && (i == 0 || !isWordChar cs[i - 1]!) then return true
  return false

/-- `k`'s text without the parentheses around it, as the receiver of a
method: in parentheses where it needs them (`Printed.asReceiver`). -/
def receiverText (src : Array Char) (k : BNode α) : String := (Tree.ofText (k.text src)).print.asReceiver true

/-- `msg` without its fix where the text of `n` has a comment, which the
fix would drop. -/
def keepComments (src : Array Char) (n : BNode α) (msg : Msg) : Msg :=
  if hasComment (textOf src n.range) then
    { msg with fixes := #[], notes := msg.notes.push "note: the fix would drop the comments in the conditional, so it has none" }
  else msg

/-- The method call `t`, which replaces `n`, in `slot` within `parent`. -/
def placedCall (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) (t : String) : String :=
  placed src n slot parent { text := t, prec := (BKind.method "").prec }

/-- `manual_abs` on `n`, a conditional in `slot` within `parent`
(`lint::manual_abs`). -/
def manualAbsAt? (src : Array Char) (ordered? : α → Option Ordered) (n : BNode α) (slot : Option Slot) (parent : Range) :
    Option (OpReport α) := do
  guard (n.kind == .ite)
  let #[c, t, e] := n.kids | none
  let .bin cop := c.kind | none
  let op ← Comparison.ofOp? cop
  let #[ca, cb] := c.kids | none
  let wf (k : BNode α) := writtenForm (textOf src k.range)
  -- `x`, and the comparison with `x` on its left.
  let (x, op) ← if wf cb == "0" then some (ca, op) else if wf ca == "0" then some (cb, op.mirror) else none
  guard (wf x).toInt?.isNone
  let negated (k : BNode α) : Bool := match k.kind, k.kids with
    | .neg, #[o] => wf o == wf x
    | _, _ => false
  let negatedThen ← if negated t && wf e == wf x then some true else if wf t == wf x && negated e then some false else none
  guard (manualAbs ((ordered? c.ref).getD .other) op negatedThen)
  let fixed := placedCall src n slot parent s!"{receiverText src x}.abs"
  return { lint := .manualAbs, ref := n.ref, msg := keepComments src n (manualAbsMsg fixed) }

/-- `manual_abs_diff` on `n`, a conditional in `slot` within `parent`
(`lint::manual_abs_diff`). -/
def manualAbsDiffAt? (src : Array Char) (ordered? : α → Option Ordered) (n : BNode α) (slot : Option Slot)
    (parent : Range) : Option (OpReport α) := do
  guard (n.kind == .ite)
  let #[c, t, e] := n.kids | none
  let (op, a, b) ← comparisonOf? src c
  let wf (k : BNode α) := writtenForm (textOf src k.range)
  let diff? (k : BNode α) : Option (String × String) := match k.kind, k.kids with
    | .bin "-", #[l, r] => some (wf l, wf r)
    | _, _ => none
  guard (manualAbsDiffRule op ((ordered? c.ref).getD .other) a b (← diff? t) (← diff? e))
  let fixed := placedCall src n slot parent s!"({textOf src t.range}).abs"
  return { lint := .manualAbsDiff, ref := n.ref, msg := keepComments src n (manualAbsDiffMsg fixed) }

/-- `manual_min_max` on `n`, a conditional in `slot` within `parent`, where
`ordered?` says what type an ordering compares (`lint::manual_min_max`).
The receiver of the fix is an operand without an integer literal, the left
one if both are. -/
def manualMinMaxAt? (src : Array Char) (ordered? : α → Option Ordered) (n : BNode α) (slot : Option Slot)
    (parent : Range) : Option (OpReport α) := do
  guard (n.kind == .ite)
  let #[c, t, e] := n.kids | none
  let (op, a, b) ← comparisonOf? src c
  let #[ca, cb] := c.kids | none
  let wf (k : BNode α) := writtenForm (textOf src k.range)
  let (m, left) ← manualMinMaxRule op ((ordered? c.ref).getD .other) a b (wf t) (wf e)
    (hasIntLiteral (textOf src ca.range)) (hasIntLiteral (textOf src cb.range))
  let (r, arg) := if left then (ca, cb) else (cb, ca)
  let fixed := placedCall src n slot parent s!"{receiverText src r}.{m.name}({textOf src arg.range})"
  return { lint := .manualMinMax, ref := n.ref, msg := keepComments src n (manualMinMaxMsg m fixed) }

/-- `manual_clamp` on `n`, a conditional in `slot` within `parent`
(`lint::manual_clamp`). -/
def manualClampAt? (src : Array Char) (ordered? : α → Option Ordered) (n : BNode α) (slot : Option Slot)
    (parent : Range) : Option (OpReport α) := do
  guard (n.kind == .ite)
  let #[c1, t1, e1] := n.kids | none
  guard (e1.kind == .ite)
  let #[c2, t2, e2] := e1.kids | none
  let wf (k : BNode α) := writtenForm (textOf src k.range)
  -- The test `x OP b then b`: `x`, the comparison with it on the left, and `b`.
  let test (c t : BNode α) : Option (BNode α × Comparison × BNode α × Int) := do
    let .bin cop := c.kind | none
    let op ← Comparison.ofOp? cop
    let #[ca, cb] := c.kids | none
    let (x, op, bound) ← if wf cb == wf t then some (ca, op, cb) else if wf ca == wf t then some (cb, op.mirror, ca) else none
    return (x, op, bound, ← intLiteral? src bound)
  let (x, op1, b1, v1) ← test c1 t1
  let (x', op2, b2, v2) ← test c2 t2
  guard (wf x == wf x' && wf e2 == wf x && !hasIntLiteral (textOf src x.range))
  guard (manualClamp ((ordered? c1.ref).getD .other) op1 op2 v1 v2)
  let (lo, hi) := if op1.below then (b1, b2) else (b2, b1)
  let fixed := placedCall src n slot parent
    s!"{receiverText src x}.max({textOf src lo.range}).min({textOf src hi.range})"
  return { lint := .manualClamp, ref := n.ref, msg := keepComments src n (manualClampMsg fixed) }

/-- `manual_rem_euclid` on `n`, a `mod` in `slot` within `parent`
(`lint::manual_rem_euclid`). -/
def manualRemEuclidAt? (src : Array Char) (n : BNode α) (slot : Option Slot) (parent : Range) : Option (OpReport α) := do
  guard (n.kind == .bin "mod")
  let #[s, k] := n.kids | none
  guard (s.kind == .bin "+")
  let #[p, q] := s.kids | none
  let wf (k : BNode α) := writtenForm (textOf src k.range)
  -- Each operand, with the divisor of a remainder.
  let summand (r : BNode α) : Summand := match r.kind, r.kids with
    | .bin "mod", #[_, d] => { text := wf r, divisor? := some (wf d) }
    | _, _ => { text := wf r, divisor? := none }
  guard (manualRemEuclidRule (summand p) (summand q) (wf k))
  let inner := if (summand p).divisor?.isSome then p else q
  let fixed := placed src n slot parent (inner.text src)
  return { lint := .manualRemEuclid, ref := n.ref, msg := manualRemEuclidMsg fixed }

/-- `modulo_one` on `n`, a `mod` (`lint::modulo_one`). -/
def moduloOneAt? (src : Array Char) (n : BNode α) : Option (OpReport α) := do
  guard (n.kind == .bin "mod")
  let #[_, k] := n.kids | none
  guard (moduloOne (intLiteral? src k))
  return { lint := .moduloOne, ref := n.ref, msg := moduloOneMsg (writtenForm (textOf src k.range)) }

/-- `min_max` on `n`, a call of `min` or `max` (`lint::min_max`). -/
def minMaxAt? (src : Array Char) (n : BNode α) : Option (OpReport α) := do
  let .method om := n.kind | none
  let outer ← MinMax.ofName? om
  let #[r, b] := n.kids | none
  let .method im := r.kind | none
  let inner ← MinMax.ofName? im
  let #[_, a] := r.kids | none
  guard (minMax inner outer (← intLiteral? src a) (← intLiteral? src b))
  return { lint := .minMax, ref := n.ref, msg := minMaxMsg inner outer (writtenForm (textOf src b.range)) }

/-- `eq_op` on `n`, a call of `min` or `max` whose receiver and argument
are written the same (`lint::eq_op_method`). -/
def eqOpMethodAt? (src : Array Char) (n : BNode α) : Option (OpReport α) := do
  let .method name := n.kind | none
  let m ← MinMax.ofName? name
  let #[r, a] := n.kids | none
  let wf (k : BNode α) := writtenForm (textOf src k.range)
  guard (eqOpMethod (wf r) (wf a))
  return { lint := .eqOp, ref := n.ref, msg := eqOpMethodMsg m (textOf src r.range) }

end Fren.Core
