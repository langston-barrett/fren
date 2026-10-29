-- keep-sorted start
import Fren.Impl
import Fren.Literate
-- keep-sorted end

/-!
# Constant folding with one variable

The spec's actual recursive expressions contain literals, one variable and
addition. Its recursive fold has a contract for every environment, proved
by Fren's Hoare induction. Lean connects these declarations to the independent
layer requirements and proves variable preservation, normalization and
idempotence on the same generated recursive expressions.
-/

open Fren.Lang

#fren_md "arith-reqs.fren"
#fren_md "arith.fren"

-- Generates the recursive contract theorem by structural induction.
#fren_check

namespace Arith

open arith

/-- The proof environment never changes the residual syntax. -/
theorem fold_env_independent (e : Expr) (rho sigma : Int) : fold e rho = fold e sigma := by
  induction e with
  | Val n => rfl
  | Var => rfl
  | Add a b iha ihb => simp only [fold, iha, ihb]

/-- A tree folded in any environment preserves the value in every environment. -/
theorem eval_fold (e : Expr) (rho x : Int) : eval (fold e rho) x = eval e x := by
  rw [fold_env_independent e rho x]
  exact Fren.Generated.arith.fold.keeps_value.holds e x

variable (rho : Int)

/-- The evaluation layer of the actual recursive expression. -/
def valueLayer (x : Int) : Expr → arith_requirements.Layer Int
  | .Val n => .Val n
  | .Var => .Var
  | .Add a b => .Add (eval a x) (eval b x)

theorem eval_meets_requirement (e : Expr) (x : Int) :
    eval e x = arith_requirements.value (valueLayer x e) x := by
  cases e <;> simp [fren_spec, eval, valueLayer, arith_requirements.value]

/-- The occurrence layer uses the same syntax with Boolean children. -/
def occurrenceLayer : Expr → arith_requirements.Layer Bool
  | .Val n => .Val n
  | .Var => .Var
  | .Add a b => .Add (uses_var? a) (uses_var? b)

theorem occurrence_meets_requirement (e : Expr) :
    uses_var? e = arith_requirements.uses_var? (occurrenceLayer e) := by
  cases e <;> simp [fren_spec, uses_var?, occurrenceLayer, arith_requirements.uses_var?]

/-- Preserve the actual operands in the independent folding-step relation. -/
def syntaxLayer : Expr → arith_requirements.Layer Expr
  | .Val n => .Val n
  | .Var => .Var
  | .Add a b => .Add a b

theorem fold_meets_step (a b : Expr) :
    arith_requirements.step? Expr (syntaxLayer (fold a rho)) (syntaxLayer (fold b rho))
      (fold a rho) (fold b rho) (syntaxLayer (fold (.Add a b) rho)) = true := by
  rw [fold]
  cases ha : fold a rho <;> cases hb : fold b rho <;>
    simp [fren_spec, syntaxLayer, arith_requirements.step?]

/-- Whether an expression is a value. -/
def isVal : Expr → Bool
  | .Val _ => true
  | .Var => false
  | .Add _ _ => false

/-- An expression has no addition of two literals. -/
def fullyFolded : Expr → Prop
  | .Val _ => True
  | .Var => True
  | .Add a b => ¬(isVal a ∧ isVal b) ∧ fullyFolded a ∧ fullyFolded b

theorem fullyFolded_fold (e : Expr) : fullyFolded (fold e rho) := by
  induction e with
  | Val n => simp [fold, fullyFolded]
  | Var => simp [fold, fullyFolded]
  | Add a b iha ihb =>
    rw [fold]
    cases ha : fold a rho <;> cases hb : fold b rho <;> simp_all [fullyFolded, isVal]

theorem uses_var_fold (e : Expr) : uses_var? (fold e rho) = uses_var? e := by
  induction e with
  | Val n => rfl
  | Var => rfl
  | Add a b iha ihb =>
    rw [fold]
    cases ha : fold a rho <;> cases hb : fold b rho <;> simp_all [uses_var?]

theorem fold_of_fullyFolded (e : Expr) : fullyFolded e → fold e rho = e := by
  induction e with
  | Val n => intro _; rfl
  | Var => intro _; rfl
  | Add a b iha ihb =>
    intro h
    obtain ⟨normal, ha, hb⟩ := h
    rw [fold, iha ha, ihb hb]
    cases a <;> cases b <;> simp_all [isVal]

theorem fold_idempotent (e : Expr) : fold (fold e rho) rho = fold e rho :=
  fold_of_fullyFolded rho _ (fullyFolded_fold rho e)

/-- `(1 + 2) + (3 + 4)`. -/
def closedSample : Expr := .Add (.Add (.Val 1) (.Val 2)) (.Add (.Val 3) (.Val 4))

example : fold closedSample 0 = .Val 10 := by decide

/-- `x + (1 + 2)` retains its variable and folds the constant subtree. -/
def sample : Expr := .Add .Var (.Add (.Val 1) (.Val 2))

example : fold sample 0 = .Add .Var (.Val 3) := by decide
example : eval (fold sample 0) 2 = 5 := by decide
example : eval (fold sample 0) 9 = 12 := by decide

#guard eval (fold sample 0) 2 == 5 && eval (fold sample 0) 9 == 12 && uses_var? (fold sample 0)
#guard eval (fold closedSample 0) 0 == 10 && fold closedSample 0 matches .Val 10

end Arith
