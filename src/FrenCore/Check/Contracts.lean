-- keep-sorted start
import FrenCore.Check.Component
-- keep-sorted end

/-!
# Application facts and function contracts

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type}

/-- What a fact that an application brings to a query is about
(`check::Fact`): that the application is at least 0, that it matches its
result type, or a postcondition of the function `f`. -/
inductive AppFact (α : Type) where
  | nat
  | type
  | postcondition (f : α)
  deriving Inhabited, BEq, Repr

/-- The functions whose postconditions are among the facts `facts`, each
once, in order (`check::query_applies`): read from what each fact is, never
from its name, which a clause shares with the user's names. -/
def queriedFns {α : Type} [BEq α] (facts : List (AppFact α)) : List α :=
  (facts.filterMap fun | .postcondition f => some f | _ => none).eraseDups

/-- The facts of the application `a` that `appFactsWith` reads, as
`AppFact`s: its function's postconditions, where `fnOf` names a function
with a contract, which both front ends' `factsOf` give it. -/
def appFactKinds {F : Type} (fnOf : F → Option Name) (a : F) : List (AppFact Name) :=
  match fnOf a with
  | some f => [.postcondition f]
  | none => []

/-- Whether an application of the function `f?` (`none` for one with no
contract) brings its facts to a query of an item that is the body or
contract of the function `own?`, if it is one (`Comp.fn?`,
`check::query_facts`): not where `f?` is that function. That covers every
query of the item, its contract's realizability among them, as the
evidence puts each of its checks at `Site.functionClause`
(`CheckResult.site`). In its own contract, each application of it is its
value (`Reqs/Check#contracts-of-uninterpreted-functions`), so a fact of one
would assume its own postconditions, among them the clause that a check of
completeness, disjointness or reachability leaves out. Of a defined
function's body it drops nothing: `fnOf` names no defined function, and a
recursive one's facts come from `recursiveQueryFacts`. Nor does it cover a
generic function's own contract: `fnOf` names no function for an
application of a generic one (#522), so there only each front end's own
substitution of the value keeps its facts out. -/
def appBrings {α : Type} [BEq α] (own? f? : Option α) : Bool := own?.isNone || f? != own?

/-- The uninterpreted functions with contracts that an item applies, each
once, in order, for its checks that ask no query (`Core.checkApplies`):
`queriedFns` of the `appFactKinds` of the item's applications `apps`, as
each front end finds them in the item, which `fnOf` names. Both front ends
take it from here, each from its own representation of the item's
applications, so that a check by random testing rests on the same
contracts in both: Lean reports no such check yet, but `#fren_check` runs
the contracts that this names for its evidence. -/
def itemContracts {α : Type} (apps : Array α) (fnOf : α → Option Name) : Array Name :=
  (queriedFns (apps.toList.flatMap (appFactKinds fnOf))).toArray

/-- The applications that a query has, of `found`, those in the facts of
the ones it has had `seen`, that it does not have yet: each that brings
its facts (`brings`) and is not among `seen`, once, in order
(`check::fact_applications`). -/
def newApps {F : Type} [BEq F] (brings : F → Bool) (seen found : List F) : List F :=
  (found.filter fun b => brings b && !seen.contains b).eraseDups

/-- The applications whose facts a query has, each with what `inside`
gives of it, its facts and the applications that they mention
(`check::fact_applications`): after `acc`, the applications of `work`,
those it has `seen` last, and then, round by round, the applications in
their facts that `newApps` adds, until a round adds none. So the facts of
an application that a fact mentions are the query's too, as `b(s) = a(s) +
1`, of `b(s)`, brings `a(s)`'s. That ends: a contract applies only the
functions declared before its own, and its own only at its parameters,
which is the application whose facts it is
(`Reqs/Lang/Items#contracts`), so each round's applications are of
functions declared before those of the round before it, but for ones the
query has. `none` where `rounds` run out first, which, with more rounds
than functions whose applications bring facts, is never. -/
def closeApps {m : Type → Type} {F α : Type} [Monad m] [BEq F] (brings : F → Bool)
    (inside : F → m (α × List F)) : Nat → List F → List F → List (F × α) → m (Option (List (F × α)))
  | _, _, [], acc => pure (some acc)
  | 0, _, _ :: _, _ => pure none
  | n + 1, seen, work@(_ :: _), acc => do
    let rs ← work.mapM inside
    let next := newApps brings seen (rs.flatMap (·.2))
    closeApps brings inside n (seen ++ next) next (acc ++ work.zip (rs.map (·.1)))

/-- The internal error where `appFactsWith`'s rounds run out, which a
contract that applies only the functions declared before its own never
lets them. -/
def factRoundsMsg : String :=
  "internal error: the applications in the facts of a query's applications did not end within the rounds"

/-- What the applications of uninterpreted functions in a query bring
(`Reqs/Check`): for each application that `appsOf` finds in the query's
own hypotheses and goal, each once, the facts that `factsOf` gives of it:
that it is at least 0, named `nat`, if its result is a `Nat`, that it
matches its result type, named `type`, if that brings a constraint, and that it
meets each postcondition of its function where its arguments meet the
preconditions, named by the postcondition. They are in one order in both
front ends: the hypotheses' in order and then the goal's, and within a
formula in the order that `appsOf` gives, which is that of a walk of the
formula that meets an application before its arguments and the arguments
from left to right; and of each application, in the order `factsOf`
gives. Both front ends give a query these and no others, so that they
depend only on its formulas: a query never has a fact about an
application that neither it nor one of these facts mentions, as of a
called procedure's expectation, and the formulas that `coverInterpreted` reads are all it
uses. And, round by round, the facts of the applications that those facts
mention, which `factAppsOf` finds in each, transitively (`closeApps`,
`check::fact_applications`).

Along with the facts, the uninterpreted functions with contracts whose
postconditions they have (`CheckResult.applies`), each once, in the
order of their applications (`queriedFns` of their `appFactKinds`).
`fnOf` gives the path of the function of an application of an
uninterpreted function with a contract, which brings its postconditions,
and `.anonymous` where it knows none, a function whose evidence is never
known, so that a pass that rests on it fails closed; and `none` for an
application that brings no postcondition, and for an instance of a generic
function, whose premise is the check that decides the instance's contract,
which is not applied yet (#522). Of the queries of the clauses of the
function `own?`, an application of that function brings nothing
(`appBrings`). `rounds` bounds the rounds, more than the functions whose
applications bring facts; `none` where they run out. Both front ends'
query builders give their queries the facts of this, and record its
functions. -/
def appFactsWith [Monad m] [BEq F] (appsOf : F → Array F) (factsOf : F → m (Array (Name × F)))
    (fnOf : F → Option Name) (factAppsOf : F → m (Array F)) (rounds : Nat) (hyps : Array (Name × F)) (goal : F)
    (own? : Option Name := none) : m (Option (Array (Name × F) × Array Name)) := do
  -- The query's own applications first, in the order above.
  let apps := (hyps.map (·.2) ++ #[goal]).foldl (init := #[]) fun acc f =>
    (appsOf f).foldl (init := acc) fun acc a => if acc.contains a then acc else acc.push a
  let brings (a : F) := appBrings own? (fnOf a)
  let apps := (apps.filter brings).toList
  let inside (a : F) : m (Array (Name × F) × List F) := do
    let facts ← factsOf a
    return (facts, (← facts.mapM fun (_, f) => factAppsOf f).toList.flatMap (·.toList))
  let some closed ← closeApps brings inside rounds apps apps [] | return none
  let found := closed.map (·.1)
  return some ((closed.toArray.map (·.2)).flatten, (queriedFns (found.flatMap (appFactKinds fnOf))).toArray)

/-- The questions that an application of the function `f` asks of its
arguments, for the precondition check (`check::application_contract`):
each of its preconditions `pres`, at the arguments, where the
application's guard holds, as `guarded` puts it. Both front ends record
these. -/
def preconditionQuestions (guarded : F → F) (f : Name) (pres : Array (Name × F)) : Array (TableGoal × F) :=
  pres.map fun (p, g) => (.precondition f p, guarded g)

/-- The facts that an application of an uninterpreted function brings of
its postconditions `posts`, each named by its postcondition, at the
arguments and the application's value (`check::application_contract`):
each holds where its preconditions `pres` imply it, as `implies` puts it.
Both front ends' `factsOf` give these, after the application's `nat`. -/
def postconditionFacts (implies : Array F → F → F) (pres : Array F) (posts : Array (Name × F)) : Array (Name × F) :=
  posts.map fun (n, q) => (n, implies pres q)

/-- The procedure that checks the realizability of the contract of the
uninterpreted function `f` (`Reqs/Check#contracts-of-uninterpreted-functions`),
whose path is its module `path`: its parameters `params` as inputs, its
value `value` as its one output, and its preconditions `pres` and
postconditions `posts`, of the value, as its assumptions and guarantees,
with `sites`, the questions about the tables and applications in its
clauses, and the groups of their source Boolean structure, which explain a
conflict in them (`branchMessages`). Both front ends check this procedure. -/
def contractComp (path f : Name) (params : Array Name) (value : Name) (pres posts : Array (Name × F))
    (sites : Array (TableSite F) := #[]) (generic : Bool := false) (branchGroups : Array (BranchGroup F) := #[])
    (memberGroups : Array (MemberGroup F) := #[]) : Comp F :=
  { path, vars := params.map (fun x => { name := x, role := .input, isPub := true }) |>.push
      { name := value, role := .output, isPub := true }
    assumes := pres, reqs := posts, expects := #[], triggers := #[], tables := sites, fn? := some f, generic
    branchGroups, memberGroups }

end Fren.Core
