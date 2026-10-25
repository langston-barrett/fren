-- keep-sorted start
import Impls.Check
import Impls.Inst
import Impls.View
import Reqs.Impl
-- keep-sorted end
open Fren.Lang

/-! # How `impl` decides (`Reqs/Impl`) -/

namespace Fren.Impls

open Fren.Core (Answer)

impl obligation: impls::obligation for (written writtenOk : Bool) (d s : Answer) {
  written? := written,
  written_ok? := writtenOk,
  decide_q := toOutcome d,
  smt_q := toOutcome s,
  verdict := toVerdict (implVerdict written writtenOk d s).1,
  names_failures? := (implVerdict written writtenOk d s).2.1,
  axiom? := (implVerdict written writtenOk d s).2.2,
}

-- One variable, given `n` terms. Over `Nat`, so a proof by cases.
impl mapping: impls::mapping for (r : Fren.Core.Role) (p : Bool) (n : Nat) {
  role := toRole r,
  is_pub? := p,
  n := n,
  accepted? := mappingAccepted #[(`x, r, p)] (Array.replicate n `x),
} by
  intro r p n _
  cases r <;> cases p <;> rcases n with _ | _ | n <;>
    simp only [fren_spec, mappingAccepted, Array.all_replicate] <;> simp [mappingOk, toRole] <;> omega

impl statement: impls::statement for (written writtenOk : Bool) (d s : Answer) {
  written? := written,
  written_ok? := writtenOk,
  decide_q := toOutcome d,
  smt_q := toOutcome s,
  added? := implAdded (implVerdict written writtenOk d s).1,
} by
  -- The instance `o` is the obligation, so its variables are the `impl` of
  -- `obligation` above.
  intro w k d s _
  refine ⟨w, k, toOutcome d, toOutcome s, toVerdict (implVerdict w k d s).1,
    (implVerdict w k d s).2.1, (implVerdict w k d s).2.2, ?_,
    ⟨rfl, rfl, rfl, rfl⟩, trivial, obligation w k d s trivial⟩
  cases w <;> cases k <;> cases d <;> cases s <;> decide

impl vacuity: impls::vacuity for (a f w : Bool) (s : Answer) {
  added? := a,
  finite? := f,
  found? := w,
  smt_q := toOutcome s,
  vacuous? := implVacuous a f w s,
  evidence? := implEvidence a (implVacuous a f w s),
}

instance : Fren.Finite Interpreted := ⟨[.abstractType, .function, .other], by intro x; cases x <;> simp⟩

def toInterpreted : Interpreted → impls.Interpreted
  | .abstractType => .AbstractType
  | .function => .Function
  | .other => .Other

-- Over `Nat`, so a proof by cases.
impl interpretation: impls::interpretation for (w : Interpreted) (e : Nat) (t ti : Bool) {
  what := toInterpreted w,
  earlier := e,
  typed? := t,
  types_interpreted? := ti,
  accepted? := interpAccepted w e t ti,
} by
  intro w e t ti _
  cases w <;> cases t <;> cases ti <;> rcases e with _ | e <;>
    simp [fren_spec, interpAccepted, toInterpreted] <;> first | decide | omega

interp impls::ItemName := Lean.Name

-- For every component's items and interpretations in scope.
impl interpreted: impls::interpreted for (u i : Array Lean.Name) {
  used := Fren.FinSet.ofArray u,
  interpreted := Fren.FinSet.ofArray i,
  accepted? := interpretedAccepted u i,
} by
  intro u i _
  simp only [fren_spec, interpretedAccepted, Fren.FinSet.subset_def, Fren.FinSet.mem_ofArray, Array.all_eq_true',
    Array.contains_iff_mem]

end Fren.Impls
