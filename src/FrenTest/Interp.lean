-- keep-sorted start
import Fren
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
