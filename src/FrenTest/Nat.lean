-- keep-sorted start
import Fren
-- keep-sorted end
open Fren.Lang

-- A `Nat` is Lean's `Nat`, widened to an `Int` with `↑`; `-` is always an
-- `Int`, so Lean's truncating subtraction never appears.
mod nat_test

pub fn count(Int): Nat

pub comp stock {
    in n: Nat
    in m: Int
    pub det out next: Nat := n + 1
    pub det out prev: Int := n - 1
    pub det out total: Int := n + m

    expect counted: count(m) + next >= 1
}

/--
info: @[reducible] def nat_test.stock.def.next : (Int → Nat) → Nat → Int → Nat → Int → Int → Prop :=
fun count n m next prev total => next = n + 1
-/
#guard_msgs in
#print nat_test.stock.def.next

/--
info: @[reducible] def nat_test.stock.def.prev : (Int → Nat) → Nat → Int → Nat → Int → Int → Prop :=
fun count n m next prev total => prev = ↑n - 1
-/
#guard_msgs in
#print nat_test.stock.def.prev

/--
info: @[reducible] def nat_test.stock.def.total : (Int → Nat) → Nat → Int → Nat → Int → Int → Prop :=
fun count n m next prev total => total = ↑n + m
-/
#guard_msgs in
#print nat_test.stock.def.total

interp count := fun i => i.toNat

-- An implementation's binder for a `Nat` input is a `Nat`.
impl successor: stock for (k : Nat) { n := k, m := 0, next := k + 1, prev := (k : Int) - 1, total := k } by
  intro k
  simp [fren_spec]

-- The function's result is at least 0 at each application, without a
-- quantified axiom.
/-- info: fren: 5 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
#fren_check
