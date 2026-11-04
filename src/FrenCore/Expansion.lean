/-! The work allowed for eager function expansion in the evaluator
(`Reqs/Eval#expansion-limit`). -/

namespace Fren.Core

/-- Expression nodes copied while reading one source item, across all
of its function expansions and binder renamings. -/
def maxExpansionNodes : Nat := 2097152

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

/-- A resource limit, rather than a failure of the evaluator's reading. -/
def expansionLimitMsg : String :=
  s!"evaluator expansion limit exceeded ({maxExpansionNodes} copied expression nodes per source item); simplify the defined functions or split the item"

end Fren.Core
