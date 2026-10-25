-- keep-sorted start
import FrenCore.Ty
-- keep-sorted end

/-!
# Typing rules (`Reqs/Lang/Expressions#types-of-operators`)

The types that operators, conditions and the branches of a conditional
need, and the errors when an expression has another. Both front ends check
an operand's type with these, over `Ty`: the `fren` command's own types,
and the Lean front end's read with `Fren.coreTy?`. A `Nat` widens to an
`Int` (`lang::widening`).
-/

namespace Fren.Core

/-- The note that `op`'s operands are `t`s. -/
def opNote (op : String) (t : Ty) : Option String := some s!"note: the operands of `{op}` are `{t.show}`s"

/-- An expression of type `found` where one of type `expected` is needed,
with `why` it is needed. -/
def typeMismatchMsg (expected found : Ty) (why : Option String := none) : Msg :=
  let hint := match expected, found with
    | .bool, .int | .bool, .nat => #["help: compare it to make a `Bool`, e.g. `x > 0` or `x != 0`"]
    | .int, .bool => #["help: to turn a `Bool` into an `Int`, write `if b? then 1 else 0`"]
    | .nat, .int => #[narrowingNote]
    | .bool, .enum p | .int, .enum p => #[s!"help: compare it with a variant to make a `Bool`, e.g. `x = {p.getString!}::Variant`"]
    | _, _ => #[]
  { code? := some "F0304", headline := s!"type mismatch: expected `{expected.show}`, found `{found.show}`"
    label? := some s!"expected `{expected.show}`, found `{found.show}`"
    notes := why.toArray ++ hint }

/-- Checks that an expression of type `found` may stand where one of type
`expected` is needed: it is one, or a `Nat` where an `Int` is
(`lang::operator_type`). -/
def checkType (expected found : Ty) (why : Option String := none) : Except Msg Unit :=
  if found.widens expected then pure () else throw (typeMismatchMsg expected found why)

/-- Checks that an operand of the arithmetic operator `op`, of type `found`,
is an `Int` or a `Nat`. -/
def checkNumber (op : String) (found : Ty) : Except Msg Unit :=
  if found == .int || found == .nat then pure ()
  else throw (typeMismatchMsg .int found (some s!"note: the operands of `{op}` are `Int`s or `Nat`s"))

/-- Checks the operator `op`, prefix if `pre`, of operands of the types `tx`
and `ty`, if one is a newtype, whose underlying type is an ordered
enumeration if `ordered`: that newtype has `op`, and both are of it
(`lang::newtype_operator`). Both front ends check an operator's operands
with this before checking them against the operator's own types, so a
newtype's error is reported as its own. -/
def checkNewtypeOperator (op : String) (pre : Bool) (tx ty : Ty) (ordered := false) : Except Msg Unit := do
  let some (p, u) := newtypeOf? tx ty | return
  unless newtypeOpAccepted (.ofOp op pre) u ordered do throw (newtypeOpMsg op p u ordered)
  unless tx == ty do throw (newtypeMixMsg op tx ty p u)

/-- Checks that the two sides of `op`, `=` or `!=`, of types `tx` and `ty`,
have one type, after widening: of a newtype, as `checkNewtypeOperator`
does. -/
def checkComparable (op : String) (tx ty : Ty) : Except Msg Unit := do
  checkNewtypeOperator op false tx ty
  if tx.widens ty || ty.widens tx then return
  let hint := match tx, ty with
    | .enum p, .int | .int, .enum p => #[s!"note: enums are not numbers", s!"help: compare with a variant, e.g. `{p.getString!}::Variant`"]
    | .bool, .int | .int, .bool => #["note: `Bool`s are not numbers: `true` and `false` are `Bool`s"]
    | _, _ => #[]
  throw { code? := some "F0305", headline := s!"cannot compare `{tx.show}` with `{ty.show}`"
          label? := some s!"`{tx.show}` and `{ty.show}`"
          notes := #[s!"note: both sides of `{op}` must have the same type"] ++ hint }

/-- The type of the operands of the ordering `op`, from the type `tx` of
its left operand, which `ordered` says is an ordered enumeration, if it is
an enumeration: a `String`, that enumeration, or else an `Int`, which a
`Nat` widens to; an error if `tx` is none of these, or is an enumeration
that is not ordered (`lang::operator_type`). Both front ends check the left
operand with this before they elaborate the right, which must then have
the type given. -/
def orderingType (op : String) (tx : Ty) (ordered : Bool) : Except Msg Ty :=
  match tx with
  | .string => pure .string
  | .enum _ => if ordered then pure tx else throw (unorderedCompareMsg op tx.show)
  | _ => do checkType .int tx (opNote op .int); pure .int

/-- Checks the operands of `op`, `union`, `inter`, `minus` or `subset`, of
types `tx` and `ty`: sets or relations, both of one type. The error is about
the first operand (`0`) or the second (`1`). -/
def checkSetOperands (op : String) (tx ty : Ty) : Except (Nat × Msg) Unit := do
  unless tx matches .set _ | .rel .. do
    throw (0, typeMismatchMsg (.set tx) tx (some s!"note: the operands of `{op}` are sets or relations"))
  unless tx == ty do throw (1, typeMismatchMsg tx ty (some s!"note: both operands of `{op}` are `{tx.show}`s"))

/-- Checks that the operands of `++` on sequences, of types `tx` and `ty`,
have one type. -/
def checkConcatOperands (tx ty : Ty) : Except Msg Unit :=
  if ty == tx then pure () else throw (typeMismatchMsg tx ty (some s!"note: the operands of `++` are `{tx.show}`s"))

/-- Checks that the branches of a conditional, of types `tx` and `ty`, have
one type, after widening, which is the conditional's (`lang::conditional`). -/
def checkBranches (tx ty : Ty) : Except Msg Unit := do
  if tx.widens ty || ty.widens tx then return
  throw { code? := some "F0306", headline := s!"the branches of `if` have different types: `{tx.show}` and `{ty.show}`"
          label? := some "branches of different types"
          notes := #["note: `if c then a else b` is `a` or `b`, so both must have the same type, or be a `Nat` and an `Int`"] }

/-- `{}`, or `[]` if `seq`, where a collection of the other kind, `expected`,
is expected. -/
def emptyKindMsg (seq : Bool) (expected : Ty) : Msg :=
  let (lit, kind, other) := if seq then ("[]", "sequence", "{}") else ("{}", "set", "[]")
  { code? := some "F0304", headline := s!"type mismatch: expected `{expected.show}`, found an empty {kind}"
    label? := some s!"expected `{expected.show}`, found `{lit}`"
    notes := #[s!"note: `{lit}` is an empty {kind}"]
    fixes := #[{ msg := s!"write `{other}` for an empty `{expected.show}`", replacement := other }] }

/-- Checks `{}`, or `[]` if `seq`, against the type `expected?` expected of
it, which gives it its type (`lang::empty_literal`): a set or relation for
`{}`, a sequence for `[]`. Without one, or with one that is no collection,
its type cannot be known (`F0324`); a collection of the other kind is a type
mismatch. -/
def checkEmptyLiteral (seq : Bool) (expected? : Option Ty) : Except Msg Ty := do
  let unknown := if seq then emptySeqTypeMsg else emptySetTypeMsg
  let some t := expected? | throw unknown
  match seq, t with
  | false, .set _ | false, .rel .. | true, .seq _ => return t
  | false, .seq _ | true, .set _ | true, .rel .. => throw (emptyKindMsg seq t)
  | _, _ => throw unknown

/-- Checks the body of an arm of a `match`, of type `t`, against the type
`t0?` of the arms before it, if one has a type: one widens to the other
(`lang::arm_type`). Returns the type of the arms so far. -/
def checkArm (t0? : Option Ty) (t : Ty) : Except Msg Ty := do
  let some t0 := t0? | return t
  unless t.widens t0 || t0.widens t do
    throw { code? := some "F0320", headline := s!"the arms of `match` have different types: `{t0.show}` and `{t.show}`"
            label? := some "arms of different types"
            notes := #["note: a `match` has the value of one of its arms, so all must have the same type, or be `Nat`s and `Int`s"] }
  return t0.join t

/-- Checks that a row's value, of type `t`, has the type `t0` of the
values before it, after widening, which is the table's
(`Reqs/Lang/Expressions#tables`). -/
def checkRowType (t0 t : Ty) : Except Msg Unit := do
  if t.widens t0 || t0.widens t then return
  throw { code? := some "F0358", headline := s!"the rows of a table have values of different types: `{t0.show}` and `{t.show}`"
          label? := some "rows of different types"
          notes := #["note: a table has the value of one of its rows, so all must have the same type, or be `Nat`s and `Int`s"] }

/-- Why a row's condition must be a `Bool`. -/
def rowConditionNote : String := "note: the condition of a row of a table is a `Bool`"

end Fren.Core
