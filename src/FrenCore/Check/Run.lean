-- keep-sorted start
import FrenCore.Check.Properties
import FrenCore.Check.Realizability
import FrenCore.Check.Sites
import FrenCore.Recursion
-- keep-sorted end

/-!
# Running and combining checks

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type} (b : Backend m F V)

/-- `inst` for each assumption of each call, in order. -/
def checkInsts (c : Comp F) : m (Array CheckResult) := do
  return (← c.insts.zipIdx.mapM fun (i, k) => i.assumes.mapM (checkInst b c k i)).flatten

/-- Whether `hs` are consistent: `sat` if there are none. -/
def consistent (hs : Array (Name × F)) : m Answer := do
  if hs.isEmpty then return .sat
  return (← b.query hs b.falseF false).answer

/-- The constraints whose `vacuity` check failed. -/
def vacuousOf (vacuities : Array CheckResult) : Array Name :=
  vacuities.filterMap fun r => if r.verdict == .fail then r.prop? else none

/-- Whether some `vacuity` query answered `sat`, its check passing: its
hypotheses are the definitions, `A`, `I` and `R`, with a trigger, so they
are satisfiable. -/
def satisfiedOf (vacuities : Array CheckResult) : Bool :=
  vacuities.any (·.verdict == .pass)

/-- `redundancy` for each assumption, then for each requirement that is not
`vacuous`, unless they are contradictory: contradictory constraints entail
everything, and a vacuous requirement is already reported
(`check::redundancy_asked`). If `satisfied`, the definitions, `A`, `I` and
`R` are known to be satisfiable (`satisfiedOf`), so neither question of
consistency is asked: its answer is `sat`. -/
def checkRedundancies (c : Comp F) (vacuous : Array Name) (satisfied : Bool := false) : m (Array CheckResult) := do
  let assumeQ ← if satisfied then pure .sat else consistent b (c.defEqs .redundancy ++ c.assumes)
  let assumes ← c.assumes.filterMapM fun a => do
    if redundancyAsked assumeQ false then
      return some (← checkRedundant b c (c.assumes.filter (·.1 != a.1)) a)
    return none
  let allQ ← if c.reqs.isEmpty || satisfied then pure .sat
    else consistent b (c.defEqs .redundancy ++ (c.hyps b ++ c.reqs))
  let reqs ← c.reqs.filterMapM fun r => do
    if redundancyAsked allQ (vacuous.contains r.1) then
      return some (← checkRedundant b c (c.hyps b ++ c.reqs.filter (·.1 != r.1)) r)
    return none
  return assumes ++ reqs

/-- `determinism` for each `det` variable. -/
def checkDets (c : Comp F) : m (Array CheckResult) :=
  c.vars.filterMapM fun v => do
    if v.isDet then return some (← checkDeterminism b c v.name)
    return none

/-- The results of `x` if `selected`, else none. -/
def ifSelected (selected : Bool) (x : m (Array α)) : m (Array α) := if selected then x else pure #[]

/-- `act`, a check, with the functions whose contracts its queries' facts
have (`CheckResult.applies`), as `applied?` gives them: the functions that
the queries since its last call applied, which it then forgets. Both front
ends' backends record them, from `appFactsWith`. Without `applied?`, `act`
itself. -/
def withApplies (applied? : Option (m (Array Name))) (act : m CheckResult) : m CheckResult :=
  match applied? with
  | none => act
  | some applied => do
    discard applied
    let r ← act
    return { r with applies := ← applied }

/-- `withApplies`, for checks run together, as all of a kind of an item:
each has the functions of all of their queries, which is conservative. -/
def withAllApplies (applied? : Option (m (Array Name))) (act : m (Array CheckResult)) : m (Array CheckResult) :=
  match applied? with
  | none => act
  | some applied => do
    discard applied
    let rs ← act
    let fs ← applied
    return rs.map fun r => { r with applies := fs }

@[simp] theorem withApplies_none (act : m CheckResult) : withApplies none act = act := rfl
@[simp] theorem withAllApplies_none (act : m (Array CheckResult)) : withAllApplies none act = act := rfl

/-- All selected checks for one procedure, in reporting order, each with the
backend `bk` gives for its kind. A realizability conflict has at most
`examples` clash notes, `none` for no limit, and none where `interprets`
says that their queries depend on an interpretation
(`Comp.realizableInterpreted`). -/
def checkComp (bk : CheckKind → Backend m F V) (c : Comp F) (kinds : Array CheckKind := CheckKind.all)
    (examples : Option Nat := some 1) (interprets : F → Bool := fun _ => false)
    (applied? : Option (m (Array Name)) := none) : m (Array CheckResult) := do
  let one := withApplies applied?
  let all := withAllApplies applied?
  let realizable ← ifSelected (kinds.contains .realizable)
    ((#[·]) <$> one (checkRealizable (bk .realizable) (c.forKind .realizable) examples interprets))
  let insts ← ifSelected (kinds.contains .inst) (all (checkInsts (bk .inst) c))
  let expects ← ifSelected (kinds.contains .expect) (c.expects.mapM fun e => one (checkExpect (bk .expect) c e))
  let covers ← ifSelected (kinds.contains .cover) (c.covers.mapM (fun g => one (checkCover (bk .cover) c g examples)))
  let vacuities ← ifSelected (kinds.contains .vacuity)
    (c.triggers.mapM (fun t => one (checkVacuity (bk .vacuity) c t examples)))
  let redundancies ←
    ifSelected (kinds.contains .redundancy)
      (all (checkRedundancies (bk .redundancy) c (vacuousOf vacuities) (satisfiedOf vacuities)))
  let dets ← ifSelected (kinds.contains .determinism) (all (checkDets (bk .determinism) c))
  let defined ← ifSelected (kinds.contains .definedness)
    (c.indexes.mapM fun s => one (checkDefinedness (bk .definedness) c s))
  let complete ← ifSelected (kinds.contains .completeness)
    ((c.tablesOf .completeness).mapM fun t => one (checkTable (bk .completeness) c t))
  let disjoint ← ifSelected (kinds.contains .disjointness)
    ((c.tablesOf .disjointness).mapM fun t => one (checkTable (bk .disjointness) c t))
  let pres ← ifSelected (kinds.contains .precondition)
    ((c.tablesOf .precondition).mapM fun t => one (checkTable (bk .precondition) c t))
  let posts ← ifSelected (kinds.contains .postcondition)
    (c.posts.mapM fun p => one (checkPostcondition (bk .postcondition) c p))
  let reach ← ifSelected (kinds.contains .reachability)
    ((c.tablesOf .reachability).mapM fun t => one (checkReach (bk .reachability) c t))
  return realizable ++ insts ++ expects ++ covers ++ vacuities ++ redundancies ++ dets ++ defined ++ complete
    ++ disjoint ++ pres ++ posts ++ reach

/-- Finalize simultaneous induction after counterexamples have been confirmed.
A clause that used an unproved sibling's hypotheses is not a reported success. -/
def recursiveResults (recursive : Bool) (results : Array CheckResult) : Array CheckResult :=
  let unproved := results.any fun r => r.kind == .postcondition && r.verdict != .pass
  results.map fun r =>
    if recursive && r.kind == .postcondition && r.verdict == .pass && !recursivePostResult true unproved then
      { r with verdict := .inconclusive, detail := .unknown "another postcondition used by simultaneous induction did not pass" }
    else r

/-- The vacuity of an item whose trait has laws, under the laws
(`r[traits.expect.lawful]`, `Reqs/Evidence#the-laws-of-a-trait`): whether
its assumptions and calls can hold together with the laws, which the
queries of its checks but realizability have. A model shows that they can.
Where they cannot, it fails, and the item's checks rest on it as they rest
on its realizability (`itemEvidence`). -/
def checkLawful (c : Comp F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .vacuity, comp := c.path, prop? := none, verdict, detail, global := true }
  let base := c.defEqs .vacuity
  let parts := hypParts .vacuity true
  -- Of each call, its bindings, and its procedure's behaviour where its
  -- assumptions hold (`HypParts.callAssumptions`).
  let call (i : Inst F) : Name × F :=
    if parts.callAssumptions then (i.name, b.conj #[i.bindings, i.behaviour])
    else (i.name, b.conj #[i.bindings, b.notF (b.conj #[b.conj (i.assumes.map (·.2)), b.notF i.behaviour])])
  let hyps := (if parts.laws then c.laws else #[]) ++ c.assumes ++ c.insts.map call
  match ← b.query (base ++ hyps) b.falseF false with
  | .sat _ => return result .pass
  | .unsat => return result .fail (.vacuousAssumptions (← minimize b base hyps b.falseF))
  | .unknown r => return result .inconclusive (.unknown r)

/-- `checkComp`, and, for an item whose trait has laws and that has
assumptions or calls, its vacuity under the laws (`checkLawful`), as both
front ends run them. -/
def checkCompLawful (bk : CheckKind → Backend m F V) (c : Comp F) (kinds : Array CheckKind := CheckKind.all)
    (examples : Option Nat := some 1) (interprets : F → Bool := fun _ => false)
    (applied? : Option (m (Array Name)) := none) : m (Array CheckResult) := do
  let rs ← checkComp bk c kinds examples interprets applied?
  -- Without assumptions or calls, it would ask of the laws alone, which
  -- is the same for every expectation of the trait.
  if c.laws.isEmpty || (c.assumes.isEmpty && c.insts.isEmpty) || !kinds.contains .vacuity then return rs
  return rs.push (← checkLawful (bk .vacuity) c)

end Fren.Core
