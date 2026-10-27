-- keep-sorted start
import Fren.Impl
import Fren.Literate
-- keep-sorted end

/-!
# Constant folding for Hutton's razor, in Lean

Evaluation and constant folding over whole expressions, by recursion, which
the spec can't state yet. An `impl` proves that folding one `Add` meets the
spec's `arith::fold_add`, and induction lifts that to the whole tree:
folding keeps every expression's value, and leaves no `Add` of two values.
-/

open Fren.Lang

-- The spec, in its module `arith`.
#fren_md "arith.fren"

namespace Arith

open arith

/-- An expression's value. -/
def eval : Expr → Int
  | .Val n => n
  | .Add a b => eval a + eval b

/-- `Add(a, b)`, folded to a value when both operands are values. -/
def foldAdd : Expr → Expr → Expr
  | .Val x, .Val y => .Val (x + y)
  | a, b => .Add a b

/-- Constant folding, from the leaves up. -/
def cfold : Expr → Expr
  | .Val n => .Val n
  | .Add a b => foldAdd (cfold a) (cfold b)

/-- Whether an expression is a value. -/
def isVal : Expr → Bool
  | .Val _ => true
  | .Add _ _ => false

-- `fold_add` is the spec's procedure, resolved from the spec's module, `arith`.
impl foldAdd_meets: fold_add for (a b : Expr) (va vb : Int) {
  a := a, b := b, va := va, vb := vb,
  folded? := isVal (foldAdd a b), value := layer (foldAdd a b) va vb
} by
  intro a b va vb h
  simp only [fren_spec] at h ⊢
  cases a <;> cases b <;> simp [foldAdd, isVal, Expr.Val.x0] at h ⊢ <;> omega

/-- Evaluating `foldAdd a b` is one layer of evaluation, over the operands'
values. -/
theorem eval_foldAdd (a b : Expr) : eval (foldAdd a b) = layer (foldAdd a b) (eval a) (eval b) := by
  cases a <;> cases b <;> simp [foldAdd, eval, layer, Expr.Val.x0]

/-- Folding keeps every expression's value, by induction, with `foldAdd_meets`
as the step. -/
theorem eval_cfold (e : Expr) : eval (cfold e) = eval e := by
  induction e with
  | Val n => rfl
  | Add a b iha ihb =>
    have h := foldAdd_meets (cfold a) (cfold b) (eval (cfold a)) (eval (cfold b)) (by
      simp only [fren_spec]
      constructor <;> intro hv <;> rw [hv] <;> simp [eval, Expr.Val.x0])
    rw [cfold, eval_foldAdd]
    simp only [fren_spec] at h ⊢
    rw [h.2, iha, ihb, eval]

/-- An expression has no `Add` of two values. -/
def folded : Expr → Prop
  | .Val _ => True
  | .Add a b => ¬(isVal a ∧ isVal b) ∧ folded a ∧ folded b

/-- Folding leaves no `Add` of two values. -/
theorem folded_cfold (e : Expr) : folded (cfold e) := by
  induction e with
  | Val n => trivial
  | Add a b iha ihb =>
    simp only [cfold]
    revert iha ihb
    cases cfold a <;> cases cfold b <;> simp_all [foldAdd, folded, isVal]

example : cfold (.Add (.Add (.Val 1) (.Val 2)) (.Add (.Val 3) (.Val 4))) = .Val 10 := by decide

end Arith
