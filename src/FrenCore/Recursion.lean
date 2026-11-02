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

/-- A simultaneous induction cannot report a dependent success when another
postcondition is unproved (`lang::recursive_post_result`). -/
def recursivePostResult (passed unproved : Bool) : Bool := passed && !unproved

/-- Recursive counterexamples require evaluation (`lang::recursive_counterexample`):
where the formulas that `confirmedFormulas` gives apply a recursive
function (`recursive`), the evaluation of its real definition on the model
must confirm them (`confirms`); and where a fact of the applications that
the query has applies one (`factsRecursive`), it is never confirmed. That
is a conservative choice, not a necessity: the model gives the values of
those facts' applications, at which the real definitions could evaluate
them, but nothing evaluates them yet, so such a check is Inconclusive even
where the model is real, as `cover big: one(l) > 100` of `fn one(l: L):
(r: Int) { ensure e: r = total(L::Cons(1, l)) }`, which `l = [200]`
meets. -/
def recursiveCounterexample (recursive confirms factsRecursive : Bool) : Bool :=
  !factsRecursive && (!recursive || confirms)

/-- The formulas whose applications of recursive functions a query reflects,
with their one-step equations and postconditions (`lang::recursion_formulas`):
the facts that its variables' types bring, `varFacts`, those of the
applications that it has, `appFacts` (`Fren.Core.appFactsWith`,
`check::fact_applications`), and then its own hypotheses, `hyps`. Both
front ends' query builders give these to their reflection, from the same
three. -/
def recursionFormulas {F : Type} (varFacts appFacts hyps : Array (Lean.Name × F)) : Array (Lean.Name × F) :=
  varFacts ++ appFacts ++ hyps

/-- The formulas that a model of a query is confirmed against, where they
apply a recursive function (`lang::recursion_formulas`,
`recursiveCounterexample`): its own hypotheses, `hyps`, with its goal; and,
where a check reports the model (`reported`), as a counterexample, a cover
goal's witness or a member's value, which are the queries that want one,
the facts that its variables' types bring, `varFacts`, whose values are
the model's variables'. A query that wants no model reports none: its
`sat` is the answer that passes its check, as a consistent assumption or
a constraint that is not redundant, and so it is confirmed against its own
formulas alone, as before the variables' facts were. Not the facts of its
applications, which `recursiveCounterexample` takes apart. -/
def confirmedFormulas {F : Type} (reported : Bool) (varFacts hyps : Array (Lean.Name × F)) :
    Array (Lean.Name × F) :=
  if reported then varFacts ++ hyps else hyps

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
