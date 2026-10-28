-- keep-sorted start
import Fren.Impl
import Fren.Literate
-- keep-sorted end

/-!
# Constant folding for Hutton's razor, in Lean

The spec's expressions, `arith.Expr`, are a recursive inductive type, and
its `arith.eval` and `arith.fold` are Lean structural recursions, which Fren
generates from their bodies. Fren checks `fold`'s postcondition, that
folding keeps the value, by induction on the expression; here Lean proves
it by the same induction, and that folding leaves no `Add` of two values.
-/

open Fren.Lang

-- The spec, in its module `arith`.
#fren_md "arith.fren"

namespace Arith

open arith

/-- Folding keeps every expression's value: the spec's `keeps_value`. -/
theorem eval_fold (e : Expr) : eval (fold e) = eval e := by
  induction e with
  | Val n => simp [fold, eval]
  | Add a b iha ihb =>
    rw [fold, eval, ← iha, ← ihb]
    split <;> (try split) <;> simp_all [eval] <;> omega

/-- Whether an expression is a value. -/
def isVal : Expr → Bool
  | .Val _ => true
  | .Add _ _ => false

/-- An expression has no `Add` of two values. -/
def fullyFolded : Expr → Prop
  | .Val _ => True
  | .Add a b => ¬(isVal a ∧ isVal b) ∧ fullyFolded a ∧ fullyFolded b

/-- Folding leaves no `Add` of two values. -/
theorem fullyFolded_fold (e : Expr) : fullyFolded (fold e) := by
  induction e with
  | Val n => simp [fold, fullyFolded]
  | Add a b iha ihb =>
    rw [fold]
    cases ha : fold a <;> cases hb : fold b <;> simp_all [fullyFolded, isVal]

/-- `(1 + 2) + (3 + 4)`. -/
def sample : Expr := .Add (.Add (.Val 1) (.Val 2)) (.Add (.Val 3) (.Val 4))

/-- Folding `(1 + 2) + (3 + 4)` gives `10`, by Lean's kernel. -/
example : fold sample = .Val 10 := by decide

-- And by the compiled code.
#guard eval (fold sample) == 10 && fold sample matches .Val 10

end Arith
