-- keep-sorted start
import Fren.Impl
import Fren.View
-- keep-sorted end

-- Lean-only behaviour of newtypes: `struct Ms(Int)` generates a structure
-- with one field, `«0»`, so that Lean too keeps an `Ms` apart from an `Int`
-- and from other newtypes; a newtype's operators are its field's.

open Fren.Lang

mod newtype_test

pub ordered struct Ms(Int)
pub struct Bytes(Int)
pub ordered struct Name(String)

/--
info: structure newtype_test.Ms : Type
number of parameters: 0
fields:
  newtype_test.Ms.«0» : Int
constructor:
  newtype_test.Ms.mk («0» : Int) : newtype_test.Ms
-/
#guard_msgs in
#print newtype_test.Ms

-- Lean rejects mixing, as Fren does.
/--
error: Type mismatch
  b
has type
  newtype_test.Bytes
but is expected to have type
  newtype_test.Ms
-/
#guard_msgs in
example (a : newtype_test.Ms) (b : newtype_test.Bytes) : Prop := a = b

comp timer {
    in elapsed: Ms
    in budget: Ms
    in n: Name
    pub det out left: Ms := budget - elapsed
    pub det out late? := elapsed > budget
    pub det out early? := n < Name("m")
}

/--
info: @[reducible] def newtype_test.timer.def.left : newtype_test.Ms →
  newtype_test.Ms → newtype_test.Name → newtype_test.Ms → Bool → Bool → Prop :=
fun elapsed budget n left late? early? => left = { «0» := budget.«0» - elapsed.«0» }
-/
#guard_msgs in
#print newtype_test.timer.def.left

/--
info: @[reducible] def newtype_test.timer.def.late? : newtype_test.Ms →
  newtype_test.Ms → newtype_test.Name → newtype_test.Ms → Bool → Bool → Prop :=
fun elapsed budget n left late? early? => late? = decide (elapsed.«0» > budget.«0»)
-/
#guard_msgs in
#print newtype_test.timer.def.late?

-- The solver proves an `impl` whose values are built with the constructor.
comp spare {
    in budget: Ms
    pub out left: Ms

    ensure r: left = budget + Ms(1)
}

#guard_msgs in
impl spare_impl: spare for (b : Int) { budget := ⟨b⟩, left := ⟨b + 1⟩ }

-- A newtype's value of another type: the `fren` command's whole message,
-- with its note and help (`test/cli/types/f0304_newtype_value.fren`).
/--
error: type mismatch: expected `Int`, found `Bool`

note: the value of `newtype_test::Ms` has type `Int`
help: to turn a `Bool` into an `Int`, write `if b? then 1 else 0`
-/
#guard_msgs in
comp wrong_value { pub out c: Ms ensure r: c = Ms(true) }

-- A counterexample shows newtypes as Fren builds them, as the `fren`
-- command does (`test/cli/commands/counterexample_newtype.fren`).
pub struct Slot { start: Ms, tags: Set(Ms) }

comp shown {
    in t: Ms
    in s: Slot
    pub det out next: Ms := t + Ms(1)

    assume pinned: t = Ms(3) and s = Slot { start := Ms(2), tags := {Ms(9), Ms(10)} }

    expect small: next < Ms(4)
}

/--
error: expectation `newtype_test::shown::small` does not hold

counterexample: t = Ms(3), s = Slot { start := Ms(2), tags := {Ms(10), Ms(9)} }, next = Ms(4)
help: strengthen the guarantees so that it follows, or correct the expectation
---
info: fren: 3 passed, 1 failed, 0 inconclusive, 0 redundant
-/
#guard_msgs in
#fren_check shown
