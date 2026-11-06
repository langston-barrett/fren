-- keep-sorted start
import FrenCore.Check.Conflicts
-- keep-sorted end

/-!
# Call assumptions, expectations and cover goals

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type} (b : Backend m F V)

/-- `inst`: an assumption of call `k`'s procedure follows from the
assumptions, `k`'s bindings and the earlier calls
(`check::instance_assumption`). -/
def checkInst (c : Comp F) (k : Nat) (i : Inst F) (a : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .inst, comp := c.path, prop? := some i.name, target? := some (i.comp, a.1), verdict, detail
      subsetTy? := (i.typed.find? (·.1 == a.1)).map (·.2) }
  let hyps := c.defEqs .inst ++ (c.hyps b k).push (i.name, i.bindings)
  let q ← b.query hyps a.2 true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    -- Inputs and earlier calls; later ones (and `i`) are unconstrained.
    let later := (c.insts.extract k).map (·.name)
    let shown v := v.isIn && v.isPub && !later.contains v.name.getRoot
    let vals ← renderModel b c.vars model shown
    let (verdict, detail) ← confirmReport b hyps a.2 model vals verdict (.counterexample vals)
    return result verdict detail
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- Observe only evaluated members in the primary model. In particular,
this never substitutes another interpretation via a second solver query. -/
def captureMembers (c : Comp F) (owner : Name) (model : Array (Name × V)) : m (Array MemberValue) := do
  let some read := b.modelBool? | return #[]
  let mut values := #[]
  for group in c.memberGroups.filter (·.owner == owner) do
    for member in group.members do
      let evaluated ← match member.evaluationGuard? with
        | none => pure (some true)
        | some guard => read model guard
      let value ← if evaluated == some true then read model (member.valueFormula?.getD member.formula) else pure none
      values := values.push {
        owner := owner
        op := group.op
        name := member.name
        evaluated? := evaluated
        value? := value
        range? := member.range?
        text := member.text
      }
  return values

/-- `expect`: the expectation follows from the assumptions, calls and
requirements (`check::expectation`). -/
def checkExpect (c : Comp F) (e : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .expect, comp := c.path, prop? := some e.1, verdict, detail }
  let hyps := c.defEqs .expect ++ (c.hyps b ++ c.reqs)
  let q ← b.query hyps e.2 true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    let vals ← renderModel b c.vars model (·.isPub)
    let (verdict, detail) ← confirmReport b hyps e.2 model vals verdict (.counterexample vals)
    return { result verdict detail with memberValues := ← captureMembers b c e.1 model }
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- `cover`: some behaviour satisfying the assumptions, calls and
requirements satisfies the cover goal, which a model of the negated goal
witnesses (`check::cover_goal`). -/
def checkCover (c : Comp F) (g : Name × F) (examples : Option Nat := some 1) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .cover, comp := c.path, prop? := some g.1, verdict, detail }
  let hyps := c.hyps b ++ c.reqs
  let goal := b.notF g.2
  let q ← b.query (c.defEqs .cover ++ hyps) goal true
  match coverVerdict q.answer, q with
  | (verdict, true, _), .sat model =>
    let vals ← renderModel b c.vars model (·.isPub)
    let (verdict, detail) ← confirmReport b (c.defEqs .cover ++ hyps) goal model vals verdict (.witness vals)
    return { result verdict detail with memberValues := ← captureMembers b c g.1 model }
  -- The core is sought only on `unsat` (`Reqs/Check#cover-goals`).
  | (verdict, _, true), _ =>
    let core ← minimize b (c.defEqs .cover) hyps goal
    let fixed := c.defEqs .cover ++ c.hyps b ++ #[(g.1.appendAfter "_goal", g.2)]
    let branches ← branchConflictsOf b c.branchGroups fixed hyps core
      ((c.vars.filter (·.isPub)).map (·.name)) examples (!c.typesInterpreted)
      (some ((c.defEqs .cover ++ c.hyps b).map (·.1))) (some g.1)
    return { result verdict (.vacuous core) with branchConflicts := branches }
  | (.inconclusive, _, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _, _), _ => return result verdict

end Fren.Core
