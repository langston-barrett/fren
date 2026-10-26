-- keep-sorted start
import Fren.Impl
-- keep-sorted end
open Fren.Lang

-- Abstract types and functions in Lean: generated definitions take a
-- parameter for each, and `interp` fixes the one every `impl` uses.
mod interp_test

type Nm
fn q?(Nm)

comp naming {
    in name: Nm
    in annotated?
    pub out accepted?

    ensure rule: accepted? iff (q?(name) or annotated?)
}

expect same: forall (a b: naming), when a.name = b.name and a.annotated? = b.annotated?, a.accepted? = b.accepted?

/-- info: interp_test.naming.ensures : (Nm : Type) → (Nm → Bool) → Nm → Bool → Bool → Prop -/
#guard_msgs in #check @interp_test.naming.ensures

/-- info: interp_test.same : (Nm : Type) → (Nm → Bool) → Prop -/
#guard_msgs in #check @interp_test.same

def accepts (n : String) (a : Bool) : Bool := n.endsWith "?" || a

/--
error: `interp_test::naming` uses `interp_test::Nm`, which has no interpretation

help: give it one with `interp interp_test::Nm := ...` before this `impl`
-/
#guard_msgs in
impl early: naming for (n : String) (a : Bool) { name := n, annotated? := a, accepted? := accepts n a }

/--
error: `interp_test::q?` mentions `interp_test::Nm`, which has no interpretation

help: interpret `interp_test::Nm` first
-/
#guard_msgs in interp q? := fun (s : String) => s.endsWith "?"

/--
error: an abstract type's interpretation must have an `Inhabited` instance

note: an abstract type has at least one value
-/
#guard_msgs in interp Nm := Empty

interp Nm := String
interp q? := fun s => s.endsWith "?"

/--
error: `interp_test::q?` is already interpreted

note: each abstract type and function has one interpretation, which every `impl` uses
-/
#guard_msgs in interp q? := fun s => s.endsWith "!"

-- Proved against the interpretation, not against what the code computes.
impl accepts_naming: naming for (n : String) (a : Bool) { name := n, annotated? := a, accepted? := accepts n a } by
  intro n a _
  simp [fren_spec, accepts]

/-- info: interp_test.Nm : Type -/
#guard_msgs in #check @interp_test.Nm

-- An interpretation under which no input satisfies the assumptions: the
-- solver, seeing the interpretation, proves it, so the `impl` holds
-- vacuously and is no evidence.
type Key
fn arity(Key): Int

set_option fren.lint.unused_assumption "allow" in
comp ranked {
    in k: Key
    pub out ok?

    assume nonneg: arity(k) >= 0
    ensure rule: ok?
}

interp Key := Int
interp arity := fun (_ : Int) => (-1 : Int)

/--
warning: `never_ranked` holds only because no values of its binders satisfy the assumptions of `interp_test::ranked`

note: it is not evidence for `interp_test::ranked`
help: check the terms it gives the inputs, and the interpretations they use
-/
#guard_msgs in
impl never_ranked: ranked for (k : Int) { k := k, ok? := true } by
  intro _ _; simp [fren_spec]

-- An interpretation of a function whose result is a pattern type must give
-- values of it: every application assumes one, so an interpretation that
-- gives 300 for an `Int is 0..=255` is rejected, and no implementation can
-- rely on it (`Reqs/Impl#interpretations`).
mod interp_typed

fn size(Int): Int is 0..=255
fn small(Int): Int is 0..=255
fn proved(Int): Int is 0..=255
fn count(Int): Nat is 1..

comp sized {
    in x: Int
    pub out y: Int
    ensure r: y = size(x)
    expect e: y <= 255
}

/--
error: could not prove that the interpretation of `interp_typed::size` gives values of its result type `Int is 0..=255`

note: `decide` does not apply, and the solver did not prove it
note: each application of `interp_typed::size` is assumed to give one
help: write a proof after `by`
-/
#guard_msgs in
interp size := fun (_ : Int) => (300 : Int)

-- The solver proves it, as an axiom.
interp small := fun (x : Int) => if x < 0 then 0 else if x > 255 then 255 else x

/-- info: 'Fren.Generated.interp_typed.small.ensures' depends on axioms: [interp_typed.small.ensures] -/
#guard_msgs in #print axioms interp_typed.small.ensures

-- Or a proof after `by`.
interp proved := fun (_ : Int) => (7 : Int) by intro _; show (0 : Int) ≤ 7 ∧ (7 : Int) ≤ 255; decide

/-- info: 'Fren.Generated.interp_typed.proved.ensures' does not depend on any axioms -/
#guard_msgs in #print axioms interp_typed.proved.ensures

-- Into `Nat`, over an `Int`, as the solver sees it.
interp count := fun (_ : Int) => (3 : Nat)

-- With postconditions too, one statement: the result type's constraint at
-- every argument, and the postconditions where the preconditions hold. An
-- interpretation that meets the postconditions but not the result type
-- adds nothing, so the function can be interpreted again.
mod interp_typed_contract

fn capped(n: Int): Int is 0..=255
    assume nonneg: n >= 0
    ensure within: capped(n) <= n

/--
error: could not prove that the interpretation of `interp_typed_contract::capped` gives values of its result type `Int is 0..=255` and meets its postconditions

note: `decide` does not apply, and the solver did not prove them
note: each application of `interp_typed_contract::capped` is assumed to give one
help: write a proof after `by`
-/
#guard_msgs in
interp capped := fun (n : Int) => n

/--
error: the proof that the interpretation of `interp_typed_contract::capped` gives values of its result type `Int is 0..=255` and meets its postconditions uses `sorry`

note: an interpretation that is not proved to give values of its result type `Int is 0..=255` and meet its postconditions adds nothing
-/
#guard_msgs in
interp capped := fun (n : Int) => n by sorry

interp capped := fun (n : Int) => if n < 0 then 0 else if n > 255 then 255 else n

/-- info: 'Fren.Generated.interp_typed_contract.capped.ensures' depends on axioms: [interp_typed_contract.capped.ensures] -/
#guard_msgs in #print axioms interp_typed_contract.capped.ensures
