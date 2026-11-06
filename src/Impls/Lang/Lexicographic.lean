-- keep-sorted start
import Impls.Check
import Impls.Lang.Types
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

def toFieldComparison : Ordering → lang.Comparison
  | .lt => .Less
  | .eq => .Equal
  | .gt => .Greater

/-- The first of `cs` that is not `eq`. -/
def firstDiffering? : List Ordering → Option Nat
  | [] => none
  | c :: cs => if c == .eq then (firstDiffering? cs).map (· + 1) else some 0

theorem lex_first : ∀ cs : List Ordering, Fren.Core.lexCompare cs = match firstDiffering? cs with
    | none => .eq
    | some i => cs.getD i .eq
  | [] => rfl
  | c :: cs => by
    cases c <;> simp [Fren.Core.lexCompare, firstDiffering?, lex_first cs] <;> split <;> simp_all

theorem differing_some : ∀ (cs : List Ordering) (i : Nat), firstDiffering? cs = some i →
    ∃ h : i < cs.length, cs[i] ≠ .eq
  | [], _, h => by simp [firstDiffering?] at h
  | c :: cs, i, h => by
    cases c with
    | eq =>
      cases hf : firstDiffering? cs with
      | none => simp [firstDiffering?, hf] at h
      | some j =>
        simp [firstDiffering?, hf] at h
        subst h
        obtain ⟨hl, hne⟩ := differing_some cs j hf
        exact ⟨by simp; omega, by simpa using hne⟩
    | lt | gt =>
      simp [firstDiffering?] at h
      subst h
      exact ⟨by simp, by simp⟩

theorem differing_le : ∀ (cs : List Ordering) (k : Nat) (hk : k < cs.length), cs[k] ≠ .eq →
    ∃ i, firstDiffering? cs = some i ∧ i ≤ k
  | [], _, hk, _ => by simp at hk
  | c :: cs, k, hk, hne => by
    cases c with
    | eq =>
      cases k with
      | zero => simp at hne
      | succ k =>
        obtain ⟨i, hi, hle⟩ := differing_le cs k (by simp at hk; omega) (by simpa using hne)
        exact ⟨i + 1, by simp [firstDiffering?, hi], by omega⟩
    | lt | gt => exact ⟨0, by simp [firstDiffering?], by omega⟩

theorem toFieldComparison_eq (c : Ordering) : toFieldComparison c = .Equal ↔ c = .eq := by
  cases c <;> simp [toFieldComparison]

-- For every sequence of fields' comparisons, by the function by which the
-- evaluator compares a record's values, or an enumeration's payloads
-- (`FrenCli.Eval.cmpV`).
impl lexicographic: lang::lexicographic for (cs : List Ordering) (k : Int) {
  fields := Fren.Seq.ofList (cs.map toFieldComparison),
  k := k,
  decider := posOr (firstDiffering? cs),
  result := toFieldComparison (Fren.Core.lexCompare cs),
} by
  intro cs k _
  simp only [fren_spec]
  have nth (i : Nat) (h : i < cs.length) : (Fren.Seq.ofList (cs.map toFieldComparison)).nth (i : Int) = toFieldComparison cs[i] := by
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using h)]; simp
  refine ⟨?_, ?_, ?_⟩
  · intro hne
    cases hf : firstDiffering? cs with
    | none => simp [hf, posOr] at hne
    | some i =>
      obtain ⟨hi, hc⟩ := differing_some cs i hf
      simp only [posOr, nth i hi]
      exact ⟨⟨by omega, by simpa using hi⟩, by rw [Ne, toFieldComparison_eq]; exact hc⟩
  · intro ⟨⟨h0, hk⟩, hne⟩
    have hk' : k.toNat < cs.length := by simp at hk; omega
    have hkk : k = ((k.toNat : Nat) : Int) := by omega
    rw [hkk, nth k.toNat hk', Ne, toFieldComparison_eq] at hne
    obtain ⟨i, hi, hle⟩ := differing_le cs k.toNat hk' hne
    simp only [hi, posOr]
    omega
  · rw [lex_first cs]
    cases hf : firstDiffering? cs with
    | none => simp [toFieldComparison, posOr]
    | some i =>
      obtain ⟨hi, _⟩ := differing_some cs i hf
      simp only [posOr]
      rw [if_neg (by omega), nth i hi]
      simp [List.getElem?_eq_getElem hi]

end Fren.Impls
