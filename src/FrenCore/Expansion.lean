/-! The work allowed for eager function expansion in the evaluator
(`Reqs/Eval#expansion-limit`). -/

namespace Fren.Core

/-- Expression nodes copied while reading one source item, across all
of its function expansions and binder renamings. -/
-- `orders_acyclic?` was the largest item of Fren's own requirements at
-- 1,587,728 visits. 2^23 gives it more than five times its measured work,
-- while bounding the copying that previously exhausted a 6 GiB scope.
def maxExpansionNodes : Nat := 8388608

/-- Spend one node of the copying budget (`eval::expansion_step`). -/
def expansionStep : Nat → Option Nat
  | 0 => none
  | n + 1 => some n

/-- Charge a tree's occurrences before copying it, including repeated
references to shared children. The work list avoids recursive descent on
the native stack, and the traversal stops as soon as the budget runs out. -/
def expansionBudget (children : α → List α) : Nat → List α → Option Nat
  | n, [] => some n
  | 0, _ :: _ => none
  | n + 1, x :: xs =>
    match _h : expansionStep (n + 1) with
    | none => none
    | some left => expansionBudget children left (children x ++ xs)
termination_by n => n
decreasing_by simp_all [expansionStep]

/-- The reservation counts occurrences, rather than distinct nodes.
For any finite tree measure satisfying the node equation, it succeeds
exactly when the entire work list fits and returns the unspent budget.
This is independent of the front end's representation and node arity. -/
theorem expansionBudget_count (children : α → List α) (nodes : α → Nat)
    (node : ∀ x, nodes x = 1 + ((children x).map nodes).sum) :
    ∀ n work, expansionBudget children n work =
      if (work.map nodes).sum ≤ n then some (n - (work.map nodes).sum) else none := by
  intro n
  induction n with
  | zero =>
    intro work
    cases work with
    | nil => simp [expansionBudget]
    | cons x xs =>
      have hx := node x
      simp only [expansionBudget, List.map_cons, List.sum_cons]
      simp only [show ¬ nodes x + (xs.map nodes).sum ≤ 0 by omega, ↓reduceIte]
  | succ n ih =>
    intro work
    cases work with
    | nil => simp [expansionBudget]
    | cons x xs =>
      have hx := node x
      simp only [expansionBudget, expansionStep]
      rw [ih]
      simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      split <;> split <;> simp_all <;> omega

/-- Language acceptance and evaluator readiness are separate. The hosted
front end does not construct the standalone evaluator's reading
(`cli::accepts`); it therefore has no evaluator-copying rejection. -/
def readerAccepted (hosted needsLean overLimit : Bool) : Bool :=
  hosted || (!needsLean && !overLimit)

/-- The common headline used by command diagnostics and their comparisons. -/
def expansionLimitHeadline : String := "evaluator expansion limit exceeded"

/-- A resource limit, rather than a failure of the evaluator's reading. -/
def expansionLimitMsg : String :=
  s!"{expansionLimitHeadline} ({maxExpansionNodes} copied expression nodes per source item); simplify the defined functions or split the item"

end Fren.Core
