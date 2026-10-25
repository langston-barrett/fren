/-!
# Condition tables (`Reqs/Lang/Expressions#tables`)

The questions that the checks of a table ask of its rows' conditions
(`Reqs/Check#completeness`, `Reqs/Check#disjointness`), and the guards of
its rows, built over each front end's own representation of a condition.
A table is a case split by conditions tried in turn, so the same questions
serve any such split, such as the arms of a `match` with guards: whether
some case always applies, and whether a case can apply after the earlier
ones fail.
-/

namespace Fren.Core

/-- A question about the rows of a table: whether some row holds, or
whether rows `i` and `j`, counted from 0 in order with `i < j`, can both
hold. -/
inductive TableGoal where
  | completeness
  | disjointness (i j : Nat)
  deriving Inhabited, BEq, Repr

/-- The guard that the earlier cases add to case `j` of a split whose
cases are tried in turn: none of the conditions `conds` of the cases before
it holds. A row's condition is evaluated under it, and its value under it
and its own condition (`lang::guard`). -/
def earlierFail (notF : α → α) (conds : Array α) (j : Nat) : Array α :=
  (conds.extract 0 j).map notF

/-- That some case of `conds` holds: the goal of completeness, and of the
exhaustiveness of a split by conditions. -/
def someCase (orF : Array α → α) (conds : Array α) : α := orF conds

/-- That all of `xs` hold, `none` if there are none. -/
def allOf? (andF : α → α → α) (xs : Array α) : Option α :=
  xs.back?.map fun x => xs.pop.foldr andF x

/-- The questions about a table whose rows other than `_` have the
conditions `conds`, each with its formula: completeness, unless it has a
`_` row (`wild`), which always holds; and the disjointness of each pair of
rows other than `_`, in order. `defined` gives, for each condition, that
the indexes in it are in range where it evaluates them, if it has any: two
rows overlap only where both conditions have values that do not rest on an
index out of range, so a condition that an earlier row guards, as `q[0] >
0` after `q = [] => ...`, does not overlap that row where it is
undefined. -/
def tableGoals (orF : Array α → α) (andF : α → α → α) (notF : α → α) (conds : Array α)
    (defined : Array (Option α)) (wild : Bool) : Array (TableGoal × α) :=
  let pairs := conds.zipIdx.flatMap fun (cj, j) =>
    (conds.extract 0 j).zipIdx.map fun (ci, i) =>
      let both := #[defined[i]?.join, defined[j]?.join].filterMap id |>.foldr andF (andF ci cj)
      (TableGoal.disjointness i j, notF both)
  (if wild then #[] else #[(.completeness, someCase orF conds)]) ++ pairs

end Fren.Core
