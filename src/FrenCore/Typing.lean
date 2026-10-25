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

/-- Checks that the two sides of `op`, `=` or `!=`, of types `tx` and `ty`,
have one type, after widening. -/
def checkComparable (op : String) (tx ty : Ty) : Except Msg Unit := do
  if tx.widens ty || ty.widens tx then return
  let hint := match tx, ty with
    | .enum p, .int | .int, .enum p => #[s!"note: enums are not numbers", s!"help: compare with a variant, e.g. `{p.getString!}::Variant`"]
    | .bool, .int | .int, .bool => #["note: `Bool`s are not numbers: `true` and `false` are `Bool`s"]
    | _, _ => #[]
  throw { code? := some "F0305", headline := s!"cannot compare `{tx.show}` with `{ty.show}`"
          label? := some s!"`{tx.show}` and `{ty.show}`"
          notes := #[s!"note: both sides of `{op}` must have the same type"] ++ hint }

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

end Fren.Core
