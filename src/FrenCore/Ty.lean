-- keep-sorted start
import FrenCore.Names
-- keep-sorted end

/-!
# Types

The types of Fren's values, as the `fren` command elaborates them, and the
rule for applications over them (`lang::application`). The Lean-hosted
front end has Lean's types instead, which its elaborator compares.
-/

namespace Fren.Core

open Lean (Name)

/-- A type of values (`lang::Ty`). -/
inductive Ty where
  | bool
  | int
  /-- `Nat`, which widens to `Int` (`lang::widening`). -/
  | nat
  | string
  /-- `Set(T)`. -/
  | set (elem : Ty)
  /-- `Rel(A, B)`. -/
  | rel (a b : Ty)
  /-- `Seq(T)`. -/
  | seq (elem : Ty)
  | enum (path : Name)
  | record (path : Name)
  /-- An abstract type. -/
  | abstract (path : Name)
  deriving Inhabited, DecidableEq

/-- The abstract type that `t` is, or that is an element type within it. -/
def Ty.abstractWithin? : Ty → Option Name
  | .abstract p => some p
  | .set t => t.abstractWithin?
  | .rel a b => a.abstractWithin? <|> b.abstractWithin?
  | .seq t => t.abstractWithin?
  | _ => none

def Ty.show : Ty → String
  | .bool => "Bool"
  | .int => "Int"
  | .nat => "Nat"
  | .string => "String"
  | .set t => s!"Set({t.show})"
  | .rel a b => s!"Rel({a.show}, {b.show})"
  | .seq t => s!"Seq({t.show})"
  | .enum p | .record p | .abstract p => showPath p

/-- Whether an expression of type `found` is accepted where `expected` is:
the same type, or a `Nat` widened to an `Int` (`lang::widening`). -/
def Ty.widens (found expected : Ty) : Bool := found == expected || (found == .nat && expected == .int)

/-- The type of a conditional or a `match` whose branches have the types
`a` and `b`, one of which widens to the other: a `Nat` with an `Int` is
widened (`lang::operator_type`). -/
def Ty.join (a b : Ty) : Ty := if a == .nat && b == .int then .int else a

/-- `t`, widened to `Int` if it is a `Nat`: the type of a member of a set
or sequence, which is never a `Nat` (`lang::nat_place`). -/
def Ty.widen : Ty → Ty
  | .nat => .int
  | t => t

/-- The type of an integer literal, from whether a `Nat` is expected where
it is (`lang::literal_type`). -/
def literalTy (natExpected : Bool) : Ty := if natExpected then .nat else .int

/-- Whether an application is accepted, from its parameters' types and its
arguments' (`lang::application`): the arguments' types after widening, as
`lang::application` takes them, so they must equal the parameters'. -/
def applicationAccepted (params args : Array Ty) : Bool := args == params

/-- The operations on integers whose result may be a `Nat`
(`lang::nat_result`). -/
inductive NatOp where
  | div
  | mod
  | min
  | max
  | abs
  deriving Inhabited, DecidableEq, Repr

/-- Whether `op` gives a `Nat`, from whether its dividend or receiver is a
`Nat`, whether the argument of `min` or `max` is, and whether the divisor of
`div` or `mod` is positive (`lang::nat_result`). -/
def natResult : NatOp → (aNat bNat positive : Bool) → Bool
  | .div, a, _, p | .mod, a, _, p => a && p
  | .min, a, b, _ | .max, a, b, _ => a && b
  | .abs, _, _, _ => false

/-- Where the type `Nat` is written (`lang::nat_place`). -/
inductive TypePlace where
  | variable
  | parameter
  | result
  | constant
  | field
  | payload
  | element
  deriving Inhabited, DecidableEq, Repr

/-- Whether `Nat` may be written at `place` (`lang::nat_place`). -/
def natPlaceAccepted : TypePlace → Bool
  | .field | .payload | .element => false
  | _ => true

/-- The note of a type mismatch where a `Nat` is expected and an `Int`
found. -/
def narrowingNote : String :=
  "note: an `Int` is never narrowed to a `Nat`, and `a - b` and `-a` are `Int`s, even of `Nat`s"

/-- An `Int` where a `Nat` is expected, which `why` explains. -/
def narrowingMsg (why : String) : Msg :=
  { code? := some "F0304", headline := "type mismatch: expected `Nat`, found `Int`"
    label? := some "expected `Nat`, found `Int`", notes := #[why, narrowingNote] }

/-- `Nat` written at `place`, where it may not be (`lang::nat_place`). -/
def natPlaceMsg (place : TypePlace) : Msg :=
  let what := match place with
    | .field => "the type of a field"
    | .payload => "the type of a payload"
    | _ => "the element type of a set, relation or sequence"
  { code? := some "F0338", headline := s!"`Nat` cannot be {what}", label? := some "a `Nat`"
    notes := #["note: for now, `Nat` is only the type of a variable, a function's parameter or result, or a constant",
      "help: use `Int`, and say where it is used that it is at least 0"] }

/-- What a `Nat` variable brings (`lang::nat_variable`). -/
inductive Brought where
  | nothing
  | assumption
  | requirement
  deriving Inhabited, DecidableEq, Repr

/-- What a `Nat` variable brings, from whether it is an output of the
component itself and whether it is defined (`lang::nat_variable`). -/
def natBrought (ownOutput defined : Bool) : Brought :=
  if defined then .nothing else if ownOutput then .requirement else .assumption

end Fren.Core
