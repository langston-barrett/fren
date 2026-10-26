/-!
# Case splits: tables and `match`es with guards (`Reqs/Lang/Expressions#tables`)

The questions that the checks ask of a split whose cases are tried in turn
(`Reqs/Check#completeness`, `Reqs/Check#disjointness`,
`Reqs/Check#reachability`), and the guards of its cases, built over each
front end's own representation of a condition. A `match` with guards is
such a split, each arm taken where its pattern matches and its guard
holds, and so is a table, whose rows are the arms `_ if C => e`: they
share their questions, whether some case is always taken, and whether a
case can be taken after the earlier ones fail. Only a table's rows are
asked whether two of them hold at once.
-/

namespace Fren.Core

/-- Which kind of split a question is about: a table, or a `match`. -/
inductive Split where
  | table
  | «match»
  deriving Inhabited, BEq, DecidableEq, Repr

/-- A question about the cases of a split: whether some case is taken
(`completeness`), whether rows `i` and `j` of a table, counted from 0 in
order with `i < j`, can both hold (`disjointness`), or whether case `j`,
counted from 0, can be taken (`reachability`). Or one about an
application of the function `f` with a precondition `p`
(`Reqs/Check#preconditions`): whether its arguments meet `p`, which is
asked where the application is evaluated, as a split's questions are
where the split is, and so is recorded, guarded and instantiated with
them by both front ends. -/
inductive TableGoal where
  | completeness (s : Split)
  | disjointness (i j : Nat)
  | precondition (f p : Lean.Name)
  | reachability (s : Split) (j : Nat)
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

/-- Whether the reachability of an arm is asked, from whether it has a
guard and whether an arm before it has one (`check::reachability_asked`). -/
def reachabilityAsked (guarded afterGuard : Bool) : Bool := guarded || afterGuard

/-- Whether the completeness of a `match` is asked, from whether its arms
without guards are exhaustive (`check::completeness_asked`). -/
def completenessAsked (unguardedExhaustive : Bool) : Bool := !unguardedExhaustive

/-- The questions about a split of kind `s` whose cases are taken where
`taken` says, each its test and guard, or `none` for a case that is taken
wherever it is tried, and of which those that have a guard are `guarded`:
completeness, if `complete` asks it, and the reachability of each case
that has a guard or follows one, in order (`check::completeness`,
`check::reachability`). `trueF` is the formula `true`. -/
def splitGoals (s : Split) (orF : Array α → α) (andF : α → α → α) (notF : α → α) (trueF : α)
    (taken : Array (Option α)) (guarded : Array Bool) (complete : Bool) : Array (TableGoal × α) :=
  let completeness := if complete then #[(TableGoal.completeness s, someCase orF (taken.map (·.getD trueF)))] else #[]
  let reach := (Array.range taken.size).filterMap fun j =>
    let afterGuard := (guarded.extract 0 j).any id
    if !reachabilityAsked (guarded[j]?.getD false) afterGuard then none else
    -- No case before it is taken, and it is.
    let fails := (taken.extract 0 j).map fun t? => notF (t?.getD trueF)
    let both := allOf? andF (fails ++ taken[j]!.toArray) |>.getD trueF
    some (TableGoal.reachability s j, notF both)
  completeness ++ reach

/-- The questions about a table whose rows other than `_` have the
conditions `conds`, each with its formula: completeness, unless it has a
`_` row (`wild`), which always holds; the disjointness of each pair of
rows other than `_`, in order; and the reachability of each row, as of the
arms `_ if C => e` that its rows are (`splitGoals`). `defined` gives, for
each condition, that the indexes in it are in range where it evaluates
them, if it has any: two rows overlap only where both conditions have
values that do not rest on an index out of range, so a condition that an
earlier row guards, as `q[0] > 0` after `q = [] => ...`, does not overlap
that row where it is undefined. -/
def tableGoals (orF : Array α → α) (andF : α → α → α) (notF : α → α) (trueF : α) (conds : Array α)
    (defined : Array (Option α)) (wild : Bool) : Array (TableGoal × α) :=
  let pairs := conds.zipIdx.flatMap fun (cj, j) =>
    (conds.extract 0 j).zipIdx.map fun (ci, i) =>
      let both := #[defined[i]?.join, defined[j]?.join].filterMap id |>.foldr andF (andF ci cj)
      (TableGoal.disjointness i j, notF both)
  let taken := conds.map some ++ (if wild then #[none] else #[])
  let guarded := conds.map (fun _ => true) ++ (if wild then #[false] else #[])
  let split := splitGoals .table orF andF notF trueF taken guarded (completenessAsked wild)
  split.filter (·.1 matches .completeness _) ++ pairs ++ split.filter (·.1 matches .reachability ..)

end Fren.Core
