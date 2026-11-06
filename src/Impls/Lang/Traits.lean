-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-! ## Traits (`Reqs/Lang/Traits`) -/

/-- What a member of a trait is, as written (`lang::TraitMemberKind`). -/
def toTraitMemberKind : Fren.Core.TraitMember → lang.TraitMemberKind
  | .method => .Method
  | .law => .Law
  | .expectation => .Expectation
  | .definedFunction => .DefinedFunction
  | .other _ => .OtherItem

-- For every member, as written, with the check that both front ends make
-- of it (`Core.traitMemberAccepted`).
impl trait_member: lang::trait_member for (k : Fren.Core.TraitMember) (p g u : Bool) {
  member := toTraitMemberKind k,
  pub? := p,
  generic? := g,
  uses? := u,
  accepted? := Fren.Core.traitMemberAccepted k p g u,
} by
  intro k p g u _
  cases k <;> cases p <;> cases g <;> cases u <;> simp [fren_spec, toTraitMemberKind, Fren.Core.traitMemberAccepted]

-- For every member, the phase in which both front ends elaborate it
-- (`Core.TraitMember.phase`, by which `Core.traitOrder` orders them).
impl trait_member_phase: lang::trait_member_phase for (k : Fren.Core.TraitMember) {
  member := toTraitMemberKind k,
  phase := (k.phase : Int),
} by
  intro k _
  cases k <;> simp [fren_spec, toTraitMemberKind, Fren.Core.TraitMember.phase]

/-- How the checks of an expectation, or of a law, are asked (`lang::CheckFlags`). -/
def toCheckFlags (f : Fren.Core.CheckFlags) : lang.CheckFlags :=
  { «in_core?» := f.inCore, «denied?» := f.denied }

-- For every expectation's flags and every law's, what both front ends give
-- the expectation (`Core.CheckFlags.withLaw`, which `withLaws` folds).
impl law_flags: lang::law_flags for (a b c d e f : Bool) {
  expectation := toCheckFlags { inCore := a, denied := b, fmfBound := c },
  law := toCheckFlags { inCore := d, denied := e, fmfBound := f },
  combined := toCheckFlags (Fren.Core.CheckFlags.withLaw { inCore := a, denied := b, fmfBound := c }
    { inCore := d, denied := e, fmfBound := f }),
} by
  intro a b c d e f _
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    simp [fren_spec, toCheckFlags, Fren.Core.CheckFlags.withLaw]

-- For every evidence setting, whether an expectation of a trait accepts it
-- (`Core.traitEvidenceAccepted`).
impl trait_expectation_evidence: lang::trait_expectation_evidence for (t e : Bool) {
  tested? := t,
  enumerated? := e,
  accepted? := Fren.Core.traitEvidenceAccepted t e,
} by
  intro t e _
  cases t <;> cases e <;> simp [fren_spec, Fren.Core.traitEvidenceAccepted]

end Fren.Impls
