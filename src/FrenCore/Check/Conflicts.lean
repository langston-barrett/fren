-- keep-sorted start
import FrenCore.Check.Hypotheses
import FrenCore.Check.Query
-- keep-sorted end

/-!
# Conflict and source-branch explanations

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type} (b : Backend m F V)

/-- Additional all-model forcing relationships under the general assumptions
and calls. The primary core may be input-local; its pins are not premises. -/
def conflictClashes (c : Comp F) (base : Array (Name × F)) (core : Array Name)
    (examples : Option Nat) (interprets : F → Bool) : m (Array Clash) :=
  if c.realizableInterpreted interprets then pure #[]
  else clashesOf b base ((c.substHyps b c.reqs).filter (core.contains ·.1)) c.clashOutputs examples

/-- One alternative of a source group. Equivalence always has the two
alternatives all-hold and none-hold, rather than a parity chain. -/
structure BranchAlternative (F : Type) where
  name : Name
  formula : F
  label : String := ""
  wanted? : Option Bool := none
  memberWanted : Array (Name × Bool) := #[]
  range? : Option Range := none
  text : String := ""

def BranchGroup.alternatives (group : BranchGroup F) : Array (BranchAlternative F) :=
  let cases : Array (BranchAlternative F) := match group.kind with
  | .disjunction => group.members.map fun member =>
    { name := member.name, formula := member.formula, range? := member.range?, text := member.text }
  | .exactlyOne => group.members.map fun chosen =>
    { name := chosen.name, formula := b.conj (group.members.map fun member =>
        if member.name == chosen.name then member.formula else b.notF member.formula)
      label := "only " ++ showAnnotationPath chosen.name ++ " holds"
      memberWanted := group.members.map fun member => (member.name, member.name == chosen.name)
      range? := chosen.range?, text := chosen.text }
  | .equivalence =>
    let operands := if group.members.size == 2 then "both operands" else "all operands"
    #[{ name := .str group.owner "all", formula := b.conj (group.members.map (·.formula))
        label := operands ++ " are true", wanted? := some true },
      { name := .str group.owner "none", formula := b.conj (group.members.map (b.notF ·.formula))
        label := operands ++ " are false", wanted? := some false }]
  cases.map fun alternative =>
    { alternative with formula := group.guard?.map (fun guard =>
        b.notF (b.conj #[guard, b.notF alternative.formula])) |>.getD alternative.formula }

/-- Explain only owners in an already minimized core. Conditional cores
keep the selected alternative as a fixed hypothesis, so dropping other
alternatives never changes or masquerades as the unconditional core.
A model of each forcing side is required before any pin/polarity query. -/
def branchConflictsOf (groups : Array (BranchGroup F)) (fixed candidates : Array (Name × F))
    (core : Array Name) (outs : Array Name) (examples : Option Nat)
    (valuesSafe : Bool := true) (premises? : Option (Array Name) := none)
    (condition? : Option Name := none) : m (Array BranchConflict) := do
  let mut found := #[]
  let mut inspected := 0
  for group in groups do
    if !core.contains group.owner then continue
    if !withinBudget inspected examples then break
    inspected := inspected + 1
    let base := fixed.filter (·.1 != group.owner)
    let rest := candidates.filter fun (n, _) => core.contains n && n != group.owner
    -- A contradiction in the premises is not an explanatory relationship.
    if (← b.query (base ++ rest) b.falseF false).answer != .sat then continue
    let mut cases := #[]
    for alternative in group.alternatives b do
      let branch := #[(alternative.name, alternative.formula)]
      let excluded ← b.query (base ++ branch ++ rest) b.falseF false
      if !excluded.isUnsat then
        cases := cases.push { name := alternative.name, label := alternative.label
                              range? := alternative.range?, text := alternative.text }
        continue
      let conditional ← minimize b (base ++ branch) rest b.falseF
      let branchModel ← b.query (base ++ branch) b.falseF true
      let impossible := branchModel.isUnsat
      let mut clashes := #[]
      if valuesSafe && !impossible then
        if let some clash ← clashAt b base (branch ++ rest) outs alternative.name then
          clashes := clashes.push clash
      let mut opposed := #[]
      if alternative.wanted?.isSome || !alternative.memberWanted.isEmpty then
        -- The shared query above already established consistency.
        for member in group.members do
          let wanted := alternative.wanted?.getD ((alternative.memberWanted.find? (·.1 == member.name)).map (·.2) |>.getD true)
          let opposite := if wanted then b.notF member.formula else member.formula
          if (← b.query (base ++ rest) opposite false).isUnsat then
            let because ← minimize b base rest opposite
            opposed := opposed.push { member := member.name, wanted, rest := because
                                      range? := member.range?, text := member.text }
      cases := cases.push { name := alternative.name, label := alternative.label, excluded := true
                            impossible, core := conditional, clashes, opposed
                            range? := alternative.range?, text := alternative.text }
    if cases.any (·.excluded) then
      found := found.push { owner := group.owner, kind := group.kind, cases
                            premises := (premises?.getD (fixed.map (·.1))).filter (· != group.owner)
                            constraints := rest.map (·.1), condition? }
  return found

/-- The source groups with the same definition substitution as the primary
realizability query. -/
def Comp.substBranchGroups (c : Comp F) : Array (BranchGroup F) :=
  c.branchGroups.map (·.map (c.subst b .realizable))

end Fren.Core
