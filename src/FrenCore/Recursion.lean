-- keep-sorted start
import FrenCore.Names
import FrenCore.Patterns
-- keep-sorted end

/-!
# Structural recursion (`lang::structural_recursion`)

Whether a defined function's uses of itself in its own body are a
structural recursion over a recursive enumeration: one parameter, the
*decreasing* one, is the same at every recursive application, and there its
argument is a binder that a `match` arm bound from a payload of that
parameter, directly or nested. Both front ends read the body into a list of
uses, and decide by `recursion`.
-/

namespace Fren.Core

/-- Where a recursive application's argument at one position comes from,
relative to the function's parameter at that same position. -/
inductive RecArg where
  /-- A binder that a `match` arm bound from a payload of the parameter,
  directly or nested: a value smaller than the parameter's. -/
  | payload
  /-- The parameter itself. -/
  | itself
  /-- Another name: another parameter, a `let`'s name, or a binder bound
  from something else. -/
  | name
  /-- Any other expression. -/
  | expr
  deriving DecidableEq, Repr, Inhabited

/-- How the function is used in its own body. -/
inductive RecForm where
  /-- Applied, outside any closure. -/
  | applied
  /-- Applied within a closure's body. -/
  | inClosure
  /-- Named as a function argument, without being applied. -/
  | passed
  deriving DecidableEq, Repr, Inhabited

/-- A use of the function in its own body: its form, and for an
application, where each argument comes from. -/
structure RecUse where
  form : RecForm
  args : List RecArg := []
  deriving DecidableEq, Repr, Inhabited

/-- Whether the use `u` is an application whose argument at position `i` is
a payload of the parameter there. -/
def RecUse.decreasesAt (u : RecUse) (i : Nat) : Bool :=
  u.form == .applied && u.args[i]? == some .payload

/-- What a function's uses of itself are. -/
inductive Recursion where
  /-- It does not use itself. -/
  | notRecursive
  /-- A structural recursion, decreasing at the parameter at this position. -/
  | structural (i : Nat)
  /-- No position decreases at every use. The use is the first by which every
  position has failed, and the position the first whose first failure is
  that use: the diagnostic names that use, and why its argument at that
  position is not a payload. -/
  | notStructural (use pos : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The index of the first of `uses` that does not decrease at position `i`. -/
def firstFailure (uses : List RecUse) (i : Nat) : Option Nat := uses.findIdx? (!·.decreasesAt i)

/-- What the uses `uses` of a function of `n` parameters are
(`lang::structural_recursion`): the decreasing parameter is the first
position at which every use decreases. -/
def recursion (n : Nat) (uses : List RecUse) : Recursion :=
  if uses.isEmpty then .notRecursive
  else match (List.range n).find? (firstFailure uses · |>.isNone) with
    | some i => .structural i
    | none =>
      let fs := (List.range n).map fun i => (firstFailure uses i).getD 0
      let k := fs.foldl max 0
      .notStructural k (fs.idxOf k)

/-- Ground applications receive postconditions and, when written, an equation.
Binder-dependent applications receive neither (`lang::recursive_facts`). -/
def recursiveFacts (introduced : Bool) (bound : Bool := false) : Bool × Bool :=
  (!bound, !bound && !introduced)

/-- Whether a recursive application brings its result type's constraint,
where the function's declared result type has one (`constrained`): with
its postconditions, wherever they are brought, so in the function's own
body too, as an induction hypothesis at each recursive application
(`lang::recursive_facts`). Both front ends call it with `constrained`
alone: the application's `bound` is decided with its postconditions, by
`recursiveFacts`, where the work queue finds applications, which gives the
result type's fact only to those that bring postconditions. -/
def recursiveResultFact (constrained : Bool) (bound : Bool := false) : Bool :=
  constrained && (recursiveFacts true bound).1

/-- A simultaneous induction cannot report a dependent success when another
postcondition is unproved (`lang::recursive_post_result`). -/
def recursivePostResult (passed unproved : Bool) : Bool := passed && !unproved

/-- Recursive counterexamples require evaluation (`lang::recursive_counterexample`):
where the query's own hypotheses and goal apply a recursive function
(`recursive`), the evaluation of its real definition on the model must
confirm them (`confirms`); and where a fact of the applications that
the query has applies one (`factsRecursive`), it is never confirmed. That
is a conservative choice, not a necessity: the model gives the values of
those facts' applications, at which the real definitions could evaluate
them, but nothing evaluates them yet, so such a check is Inconclusive even
where the model is real, as `cover big: one(l) > 100` of `fn one(l: L):
(r: Int) { ensure e: r = total(L::Cons(1, l)) }`, which `l = [200]`
meets. -/
def recursiveCounterexample (recursive confirms factsRecursive : Bool) : Bool :=
  !factsRecursive && (!recursive || confirms)

/-- Whether a check reports the solver's model as a counterexample
(`lang::counterexample_confirmed`), from the query's own hypotheses `hyps`
and its goal `goal`, each as the solver has it: whether it applies a
recursive function, and what evaluation of the real definitions gives it at
the model, `none` where evaluation gives nothing. It applies a recursive
function where any of them does, as the solver's formula has it, whether or
not evaluation can read the formula, so a model that evaluation refutes or
cannot evaluate is never a failure: the goal of a subset type's obligation
at a recursive application, which the evaluator has no formula of, is one
(#693). -/
def counterexampleReported (hyps : Array (Bool × Option Bool)) (goal : Bool × Option Bool)
    (factsRecursive : Bool) : Bool :=
  recursiveCounterexample (hyps.any (·.1) || goal.1)
    (hyps.all (·.2 == some true) && goal.2 == some false) factsRecursive

/-- The formulas whose applications of recursive functions a query reflects,
with their one-step equations and postconditions (`lang::recursion_formulas`):
the facts that its variables' types bring, `varFacts`, those of the
applications that it has, `appFacts` (`Fren.Core.appFactsWith`,
`check::fact_applications`), and then its own hypotheses, `hyps`. Both
front ends' query builders give these to their reflection, from the same
three. -/
def recursionFormulas {F : Type} (varFacts appFacts hyps : Array (Lean.Name × F)) : Array (Lean.Name × F) :=
  varFacts ++ appFacts ++ hyps

/-! ## Merging the facts found on several paths (`lang::merged_facts`) -/

/-- The weakest of the paths `ps`, with one more, `p`, to the same fact,
where `within q p` says that `q`'s guards are among `p`'s, so that where
`p`'s hold, `q`'s do (`mergeGuarded`): unchanged if one of them is within
`p`, and otherwise those of them that `p` is not within, then `p`. -/
def addPath {P : Type} (within : P → P → Bool) (ps : List P) (p : P) : List P :=
  if ps.any (within · p) then ps else ps.filter (!within p ·) ++ [p]

/-- The facts merged so far, `acc`, with one more found on a path, `x`
(`mergeGuarded`). -/
def mergeStep {F P : Type} [BEq F] (within : P → P → Bool) (acc : List (F × List P)) (x : F × P) :
    List (F × List P) :=
  if acc.any (·.1 == x.1) then acc.map fun e => (e.1, if e.1 == x.1 then addPath within e.2 x.2 else e.2)
  else acc ++ [(x.1, [x.2])]

/-- The facts `found` of a query's recursive applications, each with a path
on which its reflection finds it (`recursiveQueryFacts`), merged
(`lang::merged_facts`): each fact once, in the order in which it is first
found, with the weakest of its paths, under the disjunction of whose guards
the query asserts it (`guardedFact`). A path whose guards are within
another's is weaker: where the other's hold, its own do, so the fact under
the other's follows from it under its own, and the merged facts are
equivalent to `found`. The reflection finds an application once on each
path to it, so without this, a fact of an application that many facts
mention would be asserted once on each of their paths, though those paths
mostly only add guards to the first. In #669's version of
`examples/stlc.fren` with contracts on `subst_all` and `free`, one query
asserted one fact of `free` 423 times, under 423 paths' guards that all had
one path's; its 1,992 asserts were 279 distinct facts. Both front ends'
`recursiveQueryFacts` call this, and `mergeGuarded_equivalent` proves the
merged facts equivalent to `found`. -/
def mergeGuarded {F P : Type} [BEq F] (within : P → P → Bool) (found : List (F × P)) : List (F × List P) :=
  found.foldl (mergeStep within) []

/-- Whether every guard of `g` is one of `h`'s, so that where `h`'s hold,
`g`'s do: `mergeGuarded`'s `within` for paths given by their guards. -/
def guardsWithin {G : Type} [BEq G] (g h : Array G) : Bool := g.all h.contains

/-- The fact `f` under the paths `ps` that `mergeGuarded` keeps: under the
guards of its only path, as `implies` puts them, or under the disjunction
`disj` of its paths' guards. A path without guards is the only one kept, so
the fact then holds unconditionally. -/
def guardedFact {F G : Type} (implies : Array G → F → F) (disj : List (Array G) → G) (f : F) :
    List (Array G) → F
  | [g] => implies g f
  | ps => implies #[disj ps] f

/-! ## Lean `match`es (`lang::recursive_match`) -/

/-- Whether the pattern `p` is one that a Lean `match` has as it is, as
`Fren.matchForm` decides (`Reqs/Generated#matches`): no literal or range,
and no or-pattern but at the top. -/
partial def Pat.leanPattern (p : Pat) (top := true) : Bool :=
  match p with
  | .wild _ => true
  | .bool _ | .int _ _ | .str _ => false
  | .ctor _ args => args.all (Pat.leanPattern · false)
  | .or alts => top && alts.all (Pat.leanPattern · true)

/-- The first of the patterns `pats` of a `match`'s arms that a Lean
`match` does not have as it is. -/
def firstNonLeanPattern? (pats : Array Pat) (guarded : Array Bool := #[]) : Option Nat :=
  (pats.zipIdx.find? fun (p, i) => !p.leanPattern || guarded[i]?.getD false).map (·.2)

/-- A structural recursion's application under a `match`, on a parameter or
a binder bound from a payload of one, that its Lean definition cannot have
as a Lean `match` (`lang::recursive_match`). -/
def recursiveMatchMsg (f : Lean.Name) : Msg :=
  { code? := some "F0449", headline := s!"recursive defined function `{showPath f}` has a `match` that Lean cannot see through"
    label? := some "this arm cannot preserve structural recursion"
    notes := #["note: a structural recursion uses unguarded constructor patterns, binders and `_`, with or-patterns only at the top",
      "help: move guards, literals, ranges or nested alternatives into the constructor arm"] }

/-- A defined function's application of itself that is not structural
recursion: `f` is the function, `param` the parameter at the position whose
argument is reported, `arg` that argument's origin, and `form` the use's
form. -/
def nonStructuralMsg (f param : Lean.Name) (form : RecForm) (arg : RecArg) : Msg :=
  let why := match form, arg with
    | .passed, _ => s!"`{showPath f}` is passed as a function, not applied"
    | .inClosure, _ => s!"`{showPath f}` is applied within a closure"
    | .applied, .itself => s!"the argument is the parameter `{param}` itself"
    | .applied, .name => s!"the argument is not bound from a payload of `{param}`"
    | .applied, .expr => s!"the argument is an expression, not a payload of `{param}`"
    | .applied, .payload => s!"the argument is a payload of `{param}`"
  { code? := some "F0447", headline := s!"defined function `{showPath f}` is not structurally recursive"
    label? := some "not on a payload of a matched parameter"
    -- The reason as a note, which the Lean-hosted front end shows, as it
    -- does not show labels.
    notes := #[s!"note: {why}","note: a defined function may apply itself only to a payload of a variant that a `match` on a parameter bound, at the same parameter in every application",
      "help: match on the parameter, and apply the function to a binder of the arm's pattern"] }

end Fren.Core
