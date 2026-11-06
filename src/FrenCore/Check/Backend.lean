-- keep-sorted start
import FrenCore.Check.Types
-- keep-sorted end

/-!
# Solver answers, verdicts and backend interface

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

inductive Outcome (V : Type) where
  /-- The goal does not follow; values of (some of) the variables. -/
  | sat (model : Array (Name × V))
  /-- The goal follows. -/
  | unsat
  | unknown (reason : String)
  deriving Inhabited

def Outcome.isUnsat : Outcome V → Bool
  | .unsat => true
  | _ => false

/-- Whether a query whose model confirmation contradicts, `contradicted`,
is asked again without the solver's simplification, where the front end
can ask it so, `canAsk` (`model::requery`). -/
def asksAgain (contradicted canAsk : Bool) : Bool := contradicted && canAsk

/-- Whether the second answer of a query asked again, `asked`, replaces
the first: where it is `sat` with a model, `againSat`, that confirmation
does not contradict, `againContradicted` (`model::requery`). -/
def keepsSecond (asked againSat againContradicted : Bool) : Bool := asked && againSat && !againContradicted

/-- The cvc5 options of a query asked again (`model::requery`): without
the simplification of its preprocessing, which solves equalities and
substitutes each solution for its variable, whose value the model then
evaluates. cvc5 1.3.2 evaluates an index out of range of a sequence of
`Bool`s, `seq.nth`, so substituted, differently from its own
interpretation of it, and so gives a model that violates its own
assertions: for `a ≠ x` and `x ≠ seq.nth q 0`, `a = x = true` and
`q = []`. Without the simplification, nothing is substituted. -/
def requeryOptions : List (String × String) := [("simplification", "none")]

/-- The answer to keep of a query, `first`, by `asksAgain` and
`keepsSecond` (`model::requery`): if confirmation contradicts its model,
`contradicted`, the answer of the query asked again, `again?`, if the
front end can ask it so, where that is `sat` with a model that
confirmation does not contradict; otherwise `first`, whose model the
report then shows to be contradicted. A model is never shown on the
second answer's word alone: it is confirmed as the first is. -/
def askedAgain {m : Type → Type} [Monad m] (first : Outcome V)
    (contradicted : Array (Name × V) → m Bool) (again? : Option (m (Outcome V))) (forced : Bool := false) :
    m (Outcome V) := do
  let .sat model := first | return first
  -- A model that gives no values contradicts nothing. With `forced`
  -- (`askAgainForced`), every other first model is taken as contradicted.
  let firstContradicted ← if model.isEmpty then pure false else if forced then pure true else contradicted model
  let asks := asksAgain firstContradicted again?.isSome
  let some again := again? | return first
  unless asks do return first
  match ← again with
  | .sat model' =>
    let againContradicted ← if model'.isEmpty then pure false else contradicted model'
    if keepsSecond asks (!model'.isEmpty) againContradicted then return .sat model' else return first
  | _ => return first

/-- The answer of a query, `first`, as both front ends decide it: the
answer that `askedAgain` keeps, and then `evaluated` of it, which
evaluates the real definitions of the recursive functions that its
formulas apply (`lang::recursive_counterexample`). The evaluation is of the
answer kept, never of the first before it is asked again, so that whether
a query is asked again does not depend on it (`Reqs/Models#asking-again`). -/
def askedAgainThen {m : Type → Type} [Monad m] (first : Outcome V)
    (contradicted : Array (Name × V) → m Bool) (again? : Option (m (Outcome V)))
    (evaluated : Outcome V → m (Outcome V)) (forced : Bool := false) : m (Outcome V) := do
  evaluated (← askedAgain first contradicted again? forced)

/-- A solver's answer, without its model (`check::Outcome`). -/
inductive Answer where
  | sat
  | unsat
  | unknown
  deriving Inhabited, BEq, DecidableEq, Repr

def Outcome.answer : Outcome V → Answer
  | .sat _ => .sat
  | .unsat => .unsat
  | .unknown _ => .unknown

/-! ## Verdicts

The decisions of the checks, separate from asking the solver. -/

/-- `realizable` from the answers to `assume_q` and `cex_q`: the verdict,
and whether to report a conflict or contradictory assumptions
(`check::realizability`). -/
def realizableVerdict (assumeQ cexQ : Answer) : Verdict × Bool × Bool :=
  if assumeQ == .unsat then (.fail, false, true)
  else match cexQ with
    | .sat => (.fail, true, false)
    | .unsat => (if assumeQ == .unknown then .inconclusive else .pass, false, false)
    | .unknown => (.inconclusive, false, false)

/-- `expect` and `inst` from the answer to their query: the verdict, and
whether to report a counterexample (`check::expectation`,
`check::instance_assumption`). -/
def expectVerdict : Answer → Verdict × Bool
  | .unsat => (.pass, false)
  | .sat => (.fail, true)
  | .unknown => (.inconclusive, false)

/-- `vacuity` and `redundancy` from the answer to their query
(`check::non_vacuity`, `check::non_redundancy`). -/
def vacuityVerdict : Answer → Verdict
  | .sat => .pass
  | .unsat => .fail
  | .unknown => .inconclusive

/-- `cover` from the answer to its query: the verdict, and whether to report
a witness or the constraints that rule the goal out (`check::cover_goal`). -/
def coverVerdict : Answer → Verdict × Bool × Bool
  | .sat => (.pass, true, false)
  | .unsat => (.fail, false, true)
  | .unknown => (.inconclusive, false, false)

/-- Whether `redundancy` is checked for a constraint, from the answer to
whether its comparison set and itself are contradictory, and whether it
failed the vacuity check (`check::redundancy_asked`). -/
def redundancyAsked (consistentQ : Answer) (vacuous : Bool) : Bool :=
  consistentQ != .unsat && !vacuous

/-- `determinism` from the answer to its query, like `expect`
(`check::determinism`). -/
def determinismVerdict : Answer → Verdict × Bool := expectVerdict

def Outcome.reason : Outcome V → String
  | .unknown r => r
  | _ => ""

/-- What the checks need from a solver. -/
structure Backend (m : Type → Type) (F V : Type) where
  /-- Can `goal` be proved from the named hypotheses? -/
  query : Array (Name × F) → (goal : F) → (wantModel : Bool) → m (Outcome V)
  /-- Read a formula from the actual returned model, without a fresh query.
  An unavailable snapshot reports unknown, never a guessed truth. -/
  modelBool? : Option (Array (Name × V) → F → m (Option Bool)) := none
  falseF : F
  notF : F → F
  conj : Array F → F
  /-- `∃ outputs, f`, over the procedure's outputs. -/
  existsOutputs : F → m F
  /-- The variables in each opaque application's arguments, in the
  output type facts and `f`, after definitions are substituted/unfolded.
  This extracts syntax; `outputQueryInCore` makes the shared decision. -/
  outputApplications? : Option (F → m (List (List String))) := none
  /-- `x = v` for variable `x`, if `v` can be used in a formula. -/
  pin : Name → V → m (Option F)
  /-- The variant of `v`, a value of the variable `x` whose type is an
  enumeration, with the formula that `x` is of that variant, its tester;
  none if `x`'s type is not an enumeration, or the formula cannot be
  built. -/
  pinVariant : Name → V → m (Option (Variant × F))
  /-- `v`, written the way Fren writes values. -/
  render : Name → V → m String
  /-- What the model of the query of the hypotheses and the goal, a
  counterexample or witness that a check reports, contradicts, evaluated in
  Fren's semantics at the values that `render` shows; none if it confirms
  the answer or leaves it undecided (`Reqs/Models#confirmation`). -/
  confirm? : Option (Array (Name × F) → F → Array (Name × V) → m (Option Contradiction)) := none
  /-- `query` asked with `requeryOptions`, for a model that confirmation
  contradicts (`askedAgain`); none if the backend cannot ask it so. -/
  again? : Option (Array (Name × F) → (goal : F) → (wantModel : Bool) → m (Outcome V)) := none
  /-- `f` with each variable `x` that is not an own parameter (call variables
  too) replaced by `primed x`, a second copy of it. -/
  prime : F → F
  /-- `x = primed x`. -/
  samePrimed : Name → F
  /-- `f` with each defined output replaced by its definition, given in
  the order of their dependencies: each definition mentions only earlier
  ones. -/
  subst : Array (Name × F) → F → F

end Fren.Core
