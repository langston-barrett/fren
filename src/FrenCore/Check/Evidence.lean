-- keep-sorted start
import FrenCore.Check.Hypotheses
-- keep-sorted end

/-!
# Interpreted witnesses and trait-law premises

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type} (b : Backend m F V)

/-- The formulas of the query of the cover goal `g` (`checkCover`): the
definitions, the assumptions, each call's bindings and the meaning of
its procedure, the requirements, and the goal. No expectation or other
cover goal is among them. -/
def Comp.coverFormulas (c : Comp F) (g : F) : Array F :=
  c.defs.map (·.2.1) ++ c.assumes.map (·.2) ++ c.insts.flatMap (fun i => #[i.bindings, i.behaviour])
    ++ c.reqs.map (·.2) ++ #[g]

/-- Whether a witness of the cover goal `n` of `c` depends on an
interpretation, so that its values are not shown (`Reqs/View#check-results`):
whether some variable's type is abstract, or some formula of its query uses
an abstract type or an uninterpreted function, as `interprets` says of a
formula. Both front ends decide it so. -/
def coverInterpreted (c : Comp F) (interprets : F → Bool) (n : Name) : Bool :=
  c.typesInterpreted || match c.covers.find? (·.1 == n) with
    | some (_, g) => (c.coverFormulas g).any interprets
    | none => false

def showComp (path : Name) : String :=
  -- Unescaped, so that an instance of a generic function shows as `pick<Int>`
  -- (`instanceName`).
  "::".intercalate (path.components.map (·.toString (escape := false)))

/-- Whether a pass of a check of kind `k` comes from an `unsat` query, a
proof, rather than from a model (`check::pass_from_unsat?`): a cover goal,
a vacuity check and a reachability question pass by a witness, and a
redundancy check by a model in which the constraint is needed. -/
def CheckKind.passFromUnsat : CheckKind → Bool
  -- A pass gives a typed behaviour: `Sound.checkCover_pass`,
  -- `checkVacuity_pass`, `checkRedundant_pass`, `checkReach_pass`.
  | .cover | .vacuity | .redundancy | .reachability => false
  -- A pass holds of every behaviour: `Sound.checkExpect_pass`,
  -- `checkInst_pass`, `checkDeterminism_pass`, `checkDefinedness_pass`,
  -- `checkTable_pass` (completeness, disjointness, preconditions),
  -- `checkPostcondition`'s, and realizability's `checkRealizable_pass`,
  -- whose queries have no laws (`queryHasLaws`).
  | _ => true

/-- Whether a verdict `v` of a check of kind `k` comes from an `unsat`
query (`check::from_unsat?`): a pass or a failure, whichever is not the
model's, and never an inconclusive verdict, which comes from neither. -/
def fromUnsat (k : CheckKind) (v : Verdict) : Bool :=
  match v with
  | .pass => k.passFromUnsat
  | .fail => !k.passFromUnsat
  | .inconclusive => false

/-- Whether the verdict `v` of a check of kind `k`, of an item whose trait
has laws (`hasLaws`), rests on the laws in a way that no check of the item
settles (`check::law_premise`): where its queries have the laws
(`CheckKind.queryHasLaws`), it comes from an `unsat` query, which laws that
cannot hold would give, and the item's vacuity under the laws was not
asked (`asked`). Where it was asked, the evidence of the item's checks
rests on it, as on its realizability (`Reqs/Evidence`). A verdict from a
model rests on nothing more: the model meets the laws. -/
def lawPremise (k : CheckKind) (v : Verdict) (hasLaws : Bool) (asked : Bool := false) : Bool :=
  hasLaws && k.queryHasLaws && fromUnsat k v && !asked

/-- Whether `r` is the vacuity of its item under its trait's laws
(`checkLawful`). -/
def CheckResult.isLawful (r : CheckResult) : Bool := r.kind == .vacuity && r.prop?.isNone

/-- `rs`, of an item whose trait has laws, with the first result at each
constraint that rests on the laws (`lawPremise`) marked, for the one
message there that says so (`lawsMsg`); none is marked where the item's vacuity
under the laws was asked. -/
def withLaws (c : Comp F) (rs : Array CheckResult) : Array CheckResult := Id.run do
  if c.laws.isEmpty then return rs
  let asked := rs.any (·.isLawful)
  let mut seen : Array (Option Name) := #[]
  let mut out := #[]
  for r in rs do
    if !r.isLawful && lawPremise r.kind r.verdict true asked && !seen.contains r.prop? then
      seen := seen.push r.prop?
      out := out.push { r with restsOnLaws? := some c.lawsOf }
    else out := out.push r
  return out

/-- `rs`, with each cover goal's result marked by `coverInterpreted`, and
each result that rests on a trait's laws by `withLaws`. Both front ends
mark their results so. -/
def withInterpreted (c : Comp F) (interprets : F → Bool) (rs : Array CheckResult) : Array CheckResult :=
  withLaws c <| rs.map fun r => if r.kind == .cover then { r with interpreted := r.prop?.any (coverInterpreted c interprets) } else r

end Fren.Core
