-- keep-sorted start
import FrenCore.Check.Conflicts
import FrenCore.Check.Decidability
-- keep-sorted end

/-!
# Realizability checks

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type} (b : Backend m F V)

/-- `realizable`: every input allowed by the assumptions has outputs
satisfying the requirements, whatever the calls do
(`check::realizability`). Defined outputs are replaced by their
definitions, so that they are never under `∃` (`check::definitions`). A
conflict comes with at most `examples` clashes of forced outputs
(`clashesOf`), `none` for no limit, and none if they would depend on an
interpretation, as `interprets` says of a formula. -/
def checkRealizableUniversal (c : Comp F) (examples : Option Nat := some 1) (interprets : F → Bool := fun _ => false) :
    m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .realizable, comp := c.path, prop? := none, target? := c.fn?.map (·, .anonymous), verdict, detail
      generic := c.generic }
  let sub := c.substHyps b
  let assumes := sub c.assumes
  let assumeQ ← b.query assumes b.falseF false
  -- `cex_q` is asked only if `assume_q` is not `unsat` (`check::realizability_protocol`).
  let body := c.subst b .realizable (b.conj (c.reqs.map (·.2)))
  let cexQ ← if assumeQ.isUnsat then pure (.unknown "not asked")
    else b.query (sub (c.hyps b)) (← b.existsOutputs body) true
  let (verdict, reportsCex, reportsVacuous) := realizableVerdict assumeQ.answer cexQ.answer
  if reportsVacuous then
    let core ← minimize b #[] assumes b.falseF
    let branches ← branchConflictsOf b (c.substBranchGroups b) #[] assumes core
      ((c.vars.filter (·.isPub)).map (·.name)) examples (!c.realizableInterpreted interprets)
    return { result verdict (.vacuousAssumptions core) with branchConflicts := branches }
  if reportsCex then
    let .sat model := cexQ | return result verdict
    let input := conflictInput c.vars model
    let pinned ← pins b input
    let core ← minimize b pinned (sub c.reqs) b.falseF
    let base := sub (c.hyps b)
    let clashes ← conflictClashes b c base core examples interprets
    let branches ← branchConflictsOf b (c.substBranchGroups b) base (sub c.reqs) core c.clashOutputs examples
      (!c.realizableInterpreted interprets)
    return { result verdict (.conflict (← renderModel b c.vars input fun v => v.isIn && v.isPub) core)
             with clashes, explanationPremises := base.map (·.1), branchConflicts := branches }
  if verdict == .inconclusive then
    -- A give-up in the assumptions query must not be hidden by a time
    -- limit or a non-core output query. Preserve the chosen query's
    -- reason even when it is empty.
    let assumptionBug := assumeQ.answer == .unknown &&
      decidableUnknown true (unknownReason assumeQ.reason) assumeQ.reason
    let useOutput := cexQ.answer == .unknown && !assumptionBug
    let applications ← match useOutput, b.outputApplications? with
      | true, some extract => extract body
      | _, _ => pure []
    let outputs := (c.vars.filter fun v => v.role == .output && !c.defs.any (·.1 == v.name)).toList.map (nameText ·.name)
    return { result verdict (.unknown (if useOutput then cexQ.reason else assumeQ.reason)) with
      outputQueryInCore := outputQueryInCore outputs applications }
  return result verdict

/-- Declaration inhabitation uses SAT only for the validated fixed carrier;
all other shapes keep the universal-input realizability protocol. -/
def checkRealizable (c : Comp F) (examples : Option Nat := some 1) (interprets : F → Bool := fun _ => false) :
    m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .realizable, comp := c.path, prop? := none, target? := c.fn?.map (·, .anonymous), verdict, detail
      generic := c.generic }
  if c.fixedInhabitation interprets then
    let fixed := c.defEqs .realizable ++ c.hyps b
    let q ← b.query (fixed ++ c.reqs) b.falseF true
    match q with
    | .sat _ => return result .pass
    | .unsat =>
      let core ← minimize b fixed c.reqs b.falseF
      return result .fail (.conflict #[] core)
    | .unknown reason => return result .inconclusive (.unknown reason)
  checkRealizableUniversal b c examples interprets

end Fren.Core
