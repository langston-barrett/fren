-- keep-sorted start
import Fren.Impl
import Fren.Literate
-- keep-sorted end

/-!
# Constant folding for Hutton's razor, in Lean

The spec gives one layer of everything: `arith.Expr E`, an expression whose
operands have the type `E`; `arith.eval`, one layer of evaluation; and
`arith.fold_add`, folding one `Add`. Here, expressions are the fixed point
of `arith.Expr`, and evaluation and folding recurse over them, using the
spec's own definitions at each layer. Folding keeps every expression's
value.
-/

open Fren.Lang

-- The spec, in its module `arith`.
#fren_md "arith.fren"

namespace Arith

open arith

/-- Expressions: the fixed point of `Expr`, each with a top layer whose
operands are expressions. -/
inductive Tree where
  | roll : Expr Tree → Tree

instance : Inhabited Tree := ⟨.roll (.Val 0)⟩

/-- An expression's top layer. -/
def Tree.top : Tree → Expr Tree
  | .roll e => e

/-- An expression's value, by `eval` at each layer. -/
def value : Tree → Int
  | .roll (.Val n) => eval (.Val n)
  | .roll (.Add a b) => eval (.Add (value a) (value b))

/-- Constant folding, from the leaves up, by `fold_add` at each `Add`. -/
def cfold : Tree → Tree
  | .roll (.Val n) => .roll (.Val n)
  | .roll (.Add a b) => .roll (fold_add Tree (cfold a).top (cfold b).top .roll)

/-- An expression is rebuilt from its top layer. -/
theorem roll_top (t : Tree) : Tree.roll t.top = t := by
  cases t; rfl

/-- Folding one `Add` keeps its value. -/
theorem value_fold_add (a b : Expr Tree) :
    value (.roll (fold_add Tree a b .roll)) = value (.roll a) + value (.roll b) := by
  cases a <;> cases b <;> simp [value, eval] <;> omega

/-- Folding keeps every expression's value. -/
theorem value_cfold (t : Tree) : value (cfold t) = value t := by
  induction t using cfold.induct with
  | case1 n => rfl
  | case2 a b iha ihb =>
    rw [cfold, value_fold_add, roll_top, roll_top, iha, ihb]
    simp [value, eval]

/-- Whether a layer is a value. -/
def isVal : Expr Tree → Bool
  | .Val _ => true
  | .Add _ _ => false

/-- An expression has no `Add` of two values. -/
def fullyFolded : Tree → Prop
  | .roll (.Val _) => True
  | .roll (.Add a b) => ¬(isVal a.top ∧ isVal b.top) ∧ fullyFolded a ∧ fullyFolded b

/-- Folding leaves no `Add` of two values. -/
theorem fullyFolded_cfold (t : Tree) : fullyFolded (cfold t) := by
  induction t using cfold.induct with
  | case1 n => trivial
  | case2 a b iha ihb =>
    rw [cfold]
    revert iha ihb
    cases cfold a with | roll ea => cases cfold b with | roll eb =>
    cases ea <;> cases eb <;> simp_all [fold_add, fullyFolded, isVal, Tree.top]

/-- `(1 + 2) + (3 + 4)`. -/
def sample : Tree :=
  .roll (.Add (.roll (.Add (.roll (.Val 1)) (.roll (.Val 2)))) (.roll (.Add (.roll (.Val 3)) (.roll (.Val 4)))))

/-- Folding `(1 + 2) + (3 + 4)` gives `10`, by Lean's kernel. -/
example : cfold sample = .roll (.Val 10) := rfl

-- And by the compiled code.
#guard value (cfold sample) == 10 && (cfold sample).top matches .Val 10

end Arith
