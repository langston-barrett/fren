-- keep-sorted start
import FrenCore.Check.Assertions
-- keep-sorted end

/-!
# Vacuity, redundancy and determinism

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type} (b : Backend m F V)

/-- `vacuity`: the trigger can hold in some behaviour satisfying the
assumptions and requirements (`check::non_vacuity`). -/
def checkVacuity (c : Comp F) (t : Name × F) (examples : Option Nat := some 1) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .vacuity, comp := c.path, prop? := some t.1, verdict, detail }
  let hyps := c.hyps b ++ c.reqs
  let goal := b.notF t.2
  let q ← b.query (c.defEqs .vacuity ++ hyps) goal (c.memberGroups.any (·.owner == t.1))
  match vacuityVerdict q.answer with
  | .fail =>
    let core ← minimize b (c.defEqs .vacuity) hyps goal
    let fixed := c.defEqs .vacuity ++ c.hyps b ++ #[(t.1.appendAfter "_trigger", t.2)]
    let branches ← branchConflictsOf b c.branchGroups fixed hyps core
      ((c.vars.filter (·.isPub)).map (·.name)) examples (!c.typesInterpreted)
      (some ((c.defEqs .vacuity ++ c.hyps b).map (·.1))) (some t.1)
    return { result .fail (.vacuous core) with branchConflicts := branches }
  | .inconclusive => return result .inconclusive (.unknown q.reason)
  | .pass =>
    let members ← match q with | .sat model => captureMembers b c t.1 model | _ => pure #[]
    return { result .pass with memberValues := members }

/-- `redundancy`: the assumption or requirement `p` does not follow from
`others`: for an assumption, the other assumptions; for a requirement, the
assumptions, calls and other requirements (`check::non_redundancy`). -/
def checkRedundant (c : Comp F) (others : Array (Name × F)) (p : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .redundancy, comp := c.path, prop? := some p.1, verdict, detail }
  let q ← b.query (c.defEqs .redundancy ++ others) p.2 false
  match vacuityVerdict q.answer with
  | .fail => return result .fail (.redundant (← minimize b (c.defEqs .redundancy) others p.2))
  | .inconclusive => return result .inconclusive (.unknown q.reason)
  | .pass => return result .pass

/-- `determinism`: any two behaviours satisfying the assumptions, calls
and requirements on the same input agree on the `det` variable `x`
(`check::determinism`). -/
def checkDeterminism (c : Comp F) (x : Name) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .determinism, comp := c.path, prop? := some x, verdict, detail }
  let once := c.defEqs .determinism ++ (c.hyps b ++ c.reqs)
  let twice := once ++ once.map fun (n, f) => (primed n, b.prime f)
  let q ← b.query twice (b.samePrimed x) true
  match determinismVerdict q.answer, q with
  | (verdict, true), .sat model =>
    let input ← renderModel b c.vars model fun v => v.isIn && v.isPub && v.name.isAtomic
    let d := .nondeterministic input (← modelValue b x model x) (← modelValue b x model (primed x))
    let (verdict, detail) ← confirmReport b twice (b.samePrimed x) model input verdict d
    return result verdict detail
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

end Fren.Core
