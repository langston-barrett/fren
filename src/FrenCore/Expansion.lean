/-! The work allowed for eager function expansion in the evaluator
(`Reqs/Eval#expansion-limit`). -/

namespace Fren.Core

/-- The native evaluator's child selection when reconstructing source
questions of an unfolded application (`eval::application_sites`): every
retained argument, then the substituted body. An argument need not occur
in the body, and repetitions remain visits. -/
def applicationParts (arguments : List α) (body : α) : List α :=
  arguments ++ [body]

/-- The separate copying and inspection allowances while reading one
source item, across expansions, binder renamings and site searches. -/
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

/-- Check the occurrences handed to later traversals, separately from
the work spent making copies. In particular, a substitution may share a
large argument without copying it (`eval::reading_size`). -/
def readingBudget (children : α → List α) (remaining : Nat) (work : List α) : Option Nat :=
  expansionBudget children remaining work

/-- Search for a marked occurrence, spending a visit before inspecting it.
`none` means the search exhausted its allowance, not that no mark exists.
The work list also bounds searches through shared or cyclic replacements. -/
def readingQuery (marked : α → Bool) (children : α → List α) : Nat → List α → Option (Bool × Nat)
  | n, [] => some (false, n)
  | 0, _ :: _ => none
  | n + 1, x :: xs =>
    if marked x then some (true, n) else readingQuery marked children n (children x ++ xs)

/-- A completed search answers the tree's question and spends at least
one visit on nonempty work. Exhaustion is possible only when the whole
tree would not fit. No recursive inspection precedes the reservation. -/
theorem readingQuery_spec (marked : α → Bool) (children : α → List α)
    (nodes : α → Nat) (contains : α → Bool)
    (node : ∀ x, nodes x = 1 + ((children x).map nodes).sum)
    (site : ∀ x, contains x = (marked x || (children x).any contains)) :
    ∀ n work, match readingQuery marked children n work with
      | some (found, left) => found = work.any contains ∧ left ≤ n ∧ (work ≠ [] → left < n)
      | none => n < (work.map nodes).sum := by
  intro n
  induction n with
  | zero =>
    intro work
    cases work with
    | nil => simp [readingQuery]
    | cons x xs =>
      have hx := node x
      simp only [readingQuery, List.map_cons, List.sum_cons]
      omega
  | succ n ih =>
    intro work
    cases work with
    | nil => simp [readingQuery]
    | cons x xs =>
      cases marked_eq : marked x with
      | false =>
        simp only [readingQuery, marked_eq, Bool.false_eq_true, ↓reduceIte]
        have hc : contains x = (children x).any contains := by rw [site]; simp [marked_eq]
        have h := ih (children x ++ xs)
        cases result : readingQuery marked children n (children x ++ xs) with
        | none =>
          simp only [result, List.map_append, List.sum_append] at h ⊢
          have hx := node x
          simp only [List.map_cons, List.sum_cons]
          omega
        | some answer =>
          rcases answer with ⟨found, left⟩
          simp only [result] at h ⊢
          rcases h with ⟨found_eq, left_le, _⟩
          refine ⟨?_, by omega, fun _ => by omega⟩
          simpa only [List.any_append, List.any_cons, hc] using found_eq
      | true =>
        have hc : contains x = true := by rw [site]; simp [marked_eq]
        simp [readingQuery, marked_eq, hc]

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

/-- The standalone reading's resource decision (`cli::accepts`), after
language acceptance. Hosted and Lean-code acceptance are decided elsewhere. -/
def readerAccepted (overLimit : Bool) : Bool := !overLimit

/-- The common headline used by command diagnostics and their comparisons. -/
def expansionLimitHeadline : String := "evaluator expansion limit exceeded"

/-- A resource limit, rather than a failure of the evaluator's reading. -/
def expansionLimitMsg : String :=
  s!"{expansionLimitHeadline} ({maxExpansionNodes} visits per source item for copying or measuring retained expressions; {maxExpansionNodes} occurrences per pattern substitution); simplify the defined functions or split the item"

end Fren.Core
