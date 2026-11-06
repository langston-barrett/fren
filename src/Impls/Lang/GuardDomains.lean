-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

def toGuardOperand : lang.GuardOperand → Fren.Core.GuardOperand
  | .Name => .name
  | .Free => .free
  | .Later => .later
def toGuardRelation : lang.GuardRelation → Fren.Core.GuardRelation
  | .Lt => .lt
  | .Le => .le
  | .Gt => .gt
  | .Ge => .ge
  | .In => .mem
  | .Other => .other
def ofGuardBound : Fren.Core.GuardBound → lang.GuardBound
  | .members => .Members
  | .lower => .Lower
  | .upper => .Upper
  | .none => .NoBound

theorem guard_bound_of_eq (a : lang.GuardOperand) (r : lang.GuardRelation) (b : lang.GuardOperand) :
    ofGuardBound (Fren.Core.guardBound (toGuardOperand a) (toGuardRelation r) (toGuardOperand b)).1 = lang.guard_bound_of a r b := by
  cases a <;> cases r <;> cases b <;> decide

/-- The position of the bound name that a side is, written alone. -/
def sideAlone (s : lang.GuardSide) : Option Nat := if 0 ≤ s.alone then some s.alone.toNat else none
/-- The positions of the bound names that a side names. -/
def sideNames (s : lang.GuardSide) : List Nat := s.names.toList.filterMap fun j => if 0 ≤ j then some j.toNat else none
/-- A conjunct as both front ends give it to `Fren.Core.boundDomain`. -/
def toCoreConjunct (c : lang.GuardConjunct) : Fren.Core.GuardConjunct lang.GuardSide := some (c.lhs, toGuardRelation c.relation, c.rhs)

theorem guard_alone_iff (s : lang.GuardSide) (k : Nat) : (sideAlone s == some k) = true ↔ s.alone = (k : Int) := by
  unfold sideAlone
  split
  · rename_i h; simp only [beq_iff_eq, Option.some.injEq]; omega
  · rename_i h; simp only [beq_iff_eq, reduceCtorEq, false_iff]; omega

theorem guard_names_iff (s : lang.GuardSide) (k : Nat) :
    (sideNames s).any (· ≥ k) = true ↔ ∃ j, j ∈ s.names ∧ j ≥ (k : Int) := by
  unfold sideNames
  simp only [List.any_eq_true, List.mem_filterMap, Seq.mem_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨n, ⟨j, hj, e⟩, hk⟩
    split at e
    · rename_i h; simp only [Option.some.injEq] at e; exact ⟨j, hj, by omega⟩
    · simp at e
  · rintro ⟨j, hj, hk⟩
    exact ⟨j.toNat, ⟨j, hj, by rw [if_pos (by omega)]⟩, by omega⟩

theorem guard_operand_eq (s : lang.GuardSide) (k : Nat) :
    Fren.Core.guardOperandOf sideAlone sideNames k s = toGuardOperand (lang.guard_operand s k) := by
  unfold Fren.Core.guardOperandOf lang.guard_operand
  by_cases h1 : s.alone = (k : Int)
  · rw [if_pos h1, if_pos ((guard_alone_iff s k).2 h1)]; rfl
  · have a : ¬ (sideAlone s == some k) = true := fun h => h1 ((guard_alone_iff s k).1 h)
    rw [if_neg h1, if_neg a]
    by_cases h2 : ∃ j, j ∈ s.names ∧ j ≥ (k : Int)
    · rw [if_pos h2, if_pos ((guard_names_iff s k).2 h2)]; rfl
    · have b : ¬ (sideNames s).any (· ≥ k) = true := fun h => h2 ((guard_names_iff s k).1 h)
      rw [if_neg h2, if_neg b]; rfl

theorem conjunct_bound_of (c : lang.GuardConjunct) (k : Nat) :
    ofGuardBound (Fren.Core.conjunctBound sideAlone sideNames k (toCoreConjunct c)).1 = lang.conjunct_bound c k := by
  simp only [Fren.Core.conjunctBound, toCoreConjunct, guard_operand_eq, lang.conjunct_bound, ← guard_bound_of_eq]

theorem ofGuardBound_inj (a b : Fren.Core.GuardBound) : (ofGuardBound a == ofGuardBound b) = (a == b) := by
  cases a <;> cases b <;> decide

theorem guard_idxOf_map (l : List Fren.Core.GuardBound) (b : Fren.Core.GuardBound) :
    (l.map ofGuardBound).idxOf? (ofGuardBound b) = l.idxOf? b := by
  simp only [List.idxOf?, List.findIdx?_map]
  congr 1; funext x; exact ofGuardBound_inj x b

theorem guard_domain_map (l : List Fren.Core.GuardBound) (n : Bool) :
    Fren.Core.guardDomainBy lang.GuardBound.Members .Lower .Upper (l.map ofGuardBound) n = Fren.Core.guardDomain l n := by
  unfold Fren.Core.guardDomain Fren.Core.guardDomainBy
  have m := guard_idxOf_map l .members; have lo := guard_idxOf_map l .lower; have up := guard_idxOf_map l .upper
  simp only [ofGuardBound] at m lo up
  rw [m, lo, up]

theorem guard_idx_some [DecidableEq β] (l : List β) (b : β) (n : Nat) :
    l.idxOf? b = some n ↔ ∃ h : n < l.length, l[n] = b ∧ ∀ j (hj : j < n), l[j] ≠ b := by
  simp [List.idxOf?, List.findIdx?_eq_some_iff_getElem]

theorem guard_idx_none [DecidableEq β] (l : List β) (b : β) : l.idxOf? b = none ↔ b ∉ l := by
  simp [List.idxOf?, List.findIdx?_eq_none_iff]
  constructor
  · intro h hm; exact absurd rfl (h b hm)
  · intro h x hx e; exact h (e ▸ hx)

section
variable (cs : List lang.GuardConjunct) (k : Int)

local notation "BS" => cs.map (fun c => lang.conjunct_bound c k)

theorem guard_nb_iff (b : lang.GuardBound) (n : Int) (hk : n ≤ cs.length) :
    (∀ j : Int, 0 ≤ j ∧ j < n → lang.conjunct_bound ((Seq.ofList cs).nth j) k ≠ b) ↔
      ∀ j (hj : j < (BS).length), (j : Int) < n → (BS)[j] ≠ b := by
  constructor
  · intro h j hj hjk
    have := h j ⟨by omega, hjk⟩
    rw [Seq.nth_of_lt _ _ (by omega) (by simp at hj ⊢; omega)] at this
    simpa using this
  · rintro h j ⟨h0, hjk⟩
    rw [Seq.nth_of_lt _ _ h0 (by simp; omega)]
    have := h j.toNat (by simp; omega) (by omega)
    simpa [Int.toNat_of_nonneg h0] using this

theorem guard_none_len_iff (b : lang.GuardBound) :
    lang.none_before? (Seq.ofList cs) k b (Seq.ofList cs).len = true ↔ (BS).idxOf? b = none := by
  simp only [lang.none_before?, decide_eq_true_eq]
  rw [guard_nb_iff _ _ _ _ (by simp), guard_idx_none]
  constructor
  · intro h hm
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
    exact h j hj (by simp at hj ⊢; omega) e
  · intro h j hj _ e
    exact h (e ▸ List.getElem_mem hj)

theorem guard_first_iff (b : lang.GuardBound) (j : Int) :
    ((0 ≤ j ∧ j < (Seq.ofList cs).len) ∧ lang.first_at? (Seq.ofList cs) k b j = true) ↔
      0 ≤ j ∧ (BS).idxOf? b = some j.toNat := by
  simp only [Seq.len_eq, Seq.toList_ofList, lang.first_at?, lang.none_before?, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h0, hl⟩, e, hn⟩
    rw [Seq.nth_of_lt _ _ h0 (by simpa using hl)] at e
    rw [guard_nb_iff _ _ _ _ (by omega)] at hn
    refine ⟨h0, (guard_idx_some _ _ _).2 ⟨by simp; omega, by simpa using e, fun i hi => hn i (by simp; omega) (by omega)⟩⟩
  · rintro ⟨h0, h⟩
    obtain ⟨hl, e, hb⟩ := (guard_idx_some _ _ _).1 h
    simp at hl
    refine ⟨⟨h0, by omega⟩, ?_, ?_⟩
    · rw [Seq.nth_of_lt _ _ h0 (by simp; omega)]; simpa using e
    · rw [guard_nb_iff _ _ _ _ (by omega)]
      intro i hi hik
      exact hb i (by omega)
end

def guardDomainOut : Fren.Core.GuardDomain → lang.DomainShape × Int × Int
  | .members k => (.Members, k, -1)
  | .range lo hi => (.Range, lo, hi)
  | .fromZero hi => (.FromZero, -1, hi)
  | .unbounded => (.Unbounded, -1, -1)

/-- The domain that the code finds, of the bound name at `k`. -/
abbrev guardDomainOf (cs : List lang.GuardConjunct) (k : Nat) (n : Bool) : lang.DomainShape × Int × Int :=
  guardDomainOut (Fren.Core.boundDomain sideAlone sideNames (cs.toArray.map toCoreConjunct) k n).1

theorem guardDomainOf_eq (cs : List lang.GuardConjunct) (k : Nat) (n : Bool) :
    guardDomainOf cs k n = guardDomainOut (Fren.Core.guardDomainBy lang.GuardBound.Members .Lower .Upper
      (cs.map fun c => lang.conjunct_bound c k) n) := by
  simp only [guardDomainOf, Fren.Core.boundDomain, ← guard_domain_map]
  congr 2
  simp [List.map_map, Function.comp_def, conjunct_bound_of]

theorem guard_domain_meets (cs : List lang.GuardConjunct) (k : Nat) (n : Bool) :
    lang.guard_domain.ensures (Seq.ofList cs) k n (guardDomainOf cs k n).1 (guardDomainOf cs k n).2.1
      (guardDomainOf cs k n).2.2 := by
  rw [guardDomainOf_eq]
  unfold lang.guard_domain.ensures lang.guard_domain.ensure.members lang.guard_domain.ensure.range
    lang.guard_domain.ensure.from_zero lang.guard_domain.ensure.unbounded
  simp only [Fren.Core.guardDomainBy]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j h
    obtain ⟨h0, e⟩ := (guard_first_iff cs k _ j).1 ⟨h.1, h.2⟩
    simp [e, guardDomainOut, Int.toNat_of_nonneg h0]
  · intro l h' h
    obtain ⟨⟨⟨⟨hl, hh⟩, hm⟩, hlo⟩, hup⟩ := h
    obtain ⟨l0, el⟩ := (guard_first_iff cs k _ l).1 ⟨hl, hlo⟩
    obtain ⟨h0, eh⟩ := (guard_first_iff cs k _ h').1 ⟨hh, hup⟩
    rw [guard_none_len_iff] at hm
    simp [hm, el, eh, guardDomainOut, Int.toNat_of_nonneg l0, Int.toNat_of_nonneg h0]
  · intro h' h
    obtain ⟨⟨⟨⟨hh, hn⟩, hm⟩, hlo⟩, hup⟩ := h
    obtain ⟨h0, eh⟩ := (guard_first_iff cs k _ h').1 ⟨hh, hup⟩
    rw [guard_none_len_iff] at hm hlo
    simp [hm, hlo, eh, hn, guardDomainOut, Int.toNat_of_nonneg h0]
  · rintro ⟨hm, hu | ⟨hn, hlo⟩⟩
    · rw [guard_none_len_iff] at hm hu
      simp only [hm, hu]
      simp [guardDomainOut]
    · rw [guard_none_len_iff] at hm hlo
      simp only [hm, hlo]
      split <;> simp_all [guardDomainOut]

-- For every conjunct, as both front ends classify its operands
-- (`Fren.Core.conjunctBound`).
impl guard_bound: lang::guard_bound for (l : lang.GuardOperand) (r : lang.GuardRelation) (h : lang.GuardOperand) {
  lhs := l,
  relation := r,
  rhs := h,
  bound := ofGuardBound (Fren.Core.guardBound (toGuardOperand l) (toGuardRelation r) (toGuardOperand h)).1,
  strict? := (Fren.Core.guardBound (toGuardOperand l) (toGuardRelation r) (toGuardOperand h)).2,
} by
  intro l r h _
  cases l <;> cases r <;> cases h <;> decide

-- For every guard, as both front ends give its conjuncts to
-- `Fren.Core.boundDomain`: each side by the bound name it is alone and those
-- it names, the domain by `List.idxOf?`, characterized by the spec's
-- `first_at?` and `none_before?`.
impl guard_domain: lang::guard_domain for (cs : List lang.GuardConjunct) (k : Nat) (n : Bool) {
  conjuncts := Fren.Seq.ofList cs,
  k := k,
  nat? := n,
  shape := (guardDomainOf cs k n).1,
  lo := (guardDomainOf cs k n).2.1,
  hi := (guardDomainOf cs k n).2.2,
} by
  intro cs k n _
  exact guard_domain_meets cs k n

end Fren.Impls
