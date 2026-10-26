-- keep-sorted start
import Fren
-- keep-sorted end
open Fren.Lang

-- Contracts in Lean (`Reqs/Generated#contracts`, `Reqs/Impl#interpretations`):
-- each clause is a definition over the function's parameters, and an
-- interpretation proves the function's postconditions.
mod contract_test

pub fn nth(q: Seq(Int), i: Int): Int := q[i]
    assume in_range: 0 <= i < q.len

/-- info: contract_test.nth.in_range : Fren.Seq Int → Int → Prop -/
#guard_msgs in #check @contract_test.nth.in_range

type Key
fn rank(k: Key): Nat
    ensure positive: rank(k) > 0

-- The clause applies the function, so it takes it, after its types.
/-- info: contract_test.rank.positive : (Key : Type) → (Key → Nat) → Key → Prop -/
#guard_msgs in #check @contract_test.rank.positive

interp Key := Bool

/--
error: the interpretation of `contract_test::rank` does not meet its postconditions: `decide` evaluates their statement to false

help: correct the interpretation, or the contract
-/
#guard_msgs in interp rank := fun (_ : Bool) => 0

-- `decide` proves it, under the preconditions.
fn level(k: Key, on?): Nat
    assume chosen: on?
    ensure positive: level(k, on?) > 0

interp level := fun b on => if on then (if b then 1 else 2) else 0

/--
info: contract_test.level.ensures : ∀ (x : contract_test.Key) (x_1 : Bool),
  contract_test.level.chosen contract_test.Key x x_1 →
    contract_test.level.positive contract_test.Key contract_test.level x x_1
-/
#guard_msgs in #check @contract_test.level.ensures

-- Over `Int`, a proof after `by`, or the solver, whose answer is an axiom.
fn succ_of(n: Int): Int
    ensure greater: succ_of(n) > n

interp succ_of := fun n => n + 1 by
  intro n
  show n + 1 > n
  omega

fn grows(n: Int): Int
    ensure bigger: grows(n) > n

interp grows := fun n => n + 2

/-- info: 'contract_test.grows.ensures' depends on axioms: [contract_test.grows.ensures] -/
#guard_msgs in #print axioms contract_test.grows.ensures
