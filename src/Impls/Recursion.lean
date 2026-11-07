-- keep-sorted start
import FrenCore.RecursionGroup
import Impls.PassEvidence
import Reqs.Lang.Recursion
-- keep-sorted end

open Fren.Lang

namespace Fren.Impls

private theorem lawfulBEq_eq (a b : BEq α) [@LawfulBEq α a] [@LawfulBEq α b] : a = b := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      congr 1
      funext x y
      apply Bool.eq_iff_iff.mpr
      exact (@beq_iff_eq α ⟨a⟩ _ x y).trans (@beq_iff_eq α ⟨b⟩ _ x y).symm

private theorem matchingClosure_beq (a b : BEq α) [ha : @LawfulBEq α a] [hb : @LawfulBEq α b]
    (marked : List α) (calls : List (α × α)) :
    @Fren.Core.Matching.closure α a ha marked calls (fun _ => true) =
      @Fren.Core.Matching.closure α b hb marked calls (fun _ => true) := by
  cases lawfulBEq_eq a b
  rfl

impl group_member: lang::group_member for (defined generic higherOrder contract : Bool) {
  defined? := defined, generic? := generic, higher_order? := higherOrder, contract? := contract,
  accepted? := Fren.Core.groupMemberAccepted defined generic higherOrder contract,
} by
  intro defined generic higherOrder contract _
  cases defined <;> cases generic <;> cases higherOrder <;> cases contract <;>
    simp [fren_spec, Fren.Core.groupMemberAccepted]

def groupParameterOf (m : Fren.Core.GroupParameter) : lang.GroupParameter :=
  { count := m.count, decreasing := m.decreasing }

def groupArgOf : Fren.Core.GroupArg → lang.GroupArg
  | .payload i => .Payload i
  | .other => .Other

def recFormOf : Fren.Core.RecForm → lang.RecForm
  | .applied => .Applied
  | .inClosure => .InClosure
  | .passed => .Passed

def groupUseOf (u : Fren.Core.GroupUse) : lang.GroupUse :=
  { caller := u.caller, callee := u.callee, form := recFormOf u.form,
    args := Fren.Seq.ofList (u.args.map groupArgOf) }

@[simp] private theorem groupArgOf_payload (a : Fren.Core.GroupArg) (i : Int) :
    groupArgOf a = lang.GroupArg.Payload i ↔ a = Fren.Core.GroupArg.payload i := by
  cases a <;> simp [groupArgOf]

private theorem forall_seq_nth {α : Type} [Inhabited α] (xs : List α) (P : α → Prop) :
    (∀ k : Int, 0 ≤ k → k < (Fren.Seq.ofList xs).len → P ((Fren.Seq.ofList xs).nth k)) ↔
      ∀ x ∈ xs, P x := by
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simpa [Fren.Seq.nth_of_lt, hi] using h i (by omega) (by simpa using hi)
  · intro h k hk₀ hk₁
    rw [Fren.Seq.nth_of_lt _ _ hk₀ (by simpa using hk₁)]
    exact h _ (List.getElem_mem _)

impl group_scope: lang::group_scope for (members : List String) (caller : Int) (target : String) {
  members := Fren.Seq.ofList members, caller := caller, target := target,
  visible? := (Fren.Core.groupTarget? members caller target).isSome,
} by
  intro members caller target _
  have exists_nth : (∃ k : Int, (0 ≤ k ∧ k < (members.length : Int)) ∧
      (Fren.Seq.ofList members).nth k = target) ↔ target ∈ members := by
    constructor
    · rintro ⟨k, hk, he⟩
      rw [Fren.Seq.nth_of_lt _ _ hk.1 (by simpa using hk.2)] at he
      exact he ▸ List.getElem_mem _
    · intro hm
      obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
      exact ⟨i, ⟨by omega, by simpa using hi⟩, by simpa [Fren.Seq.nth_of_lt, hi] using he⟩
  simp [fren_spec, Fren.Core.groupTarget?_isSome, Fren.Core.groupVisible, exists_nth]

impl group_dependencies: lang::group_dependencies for (flags : List Bool) (uses : List Fren.Core.GroupUse) {
  marked := Fren.FinSet.ofList (Fren.Core.groupMarked flags),
  calls := Fren.FinSet.ofList (uses.map fun u => (u.caller, u.callee)),
  affected := Fren.FinSet.ofList (Fren.Core.groupInherited flags uses),
} by
  intro flags uses _
  let marked := Fren.Core.groupMarked flags
  let calls := uses.map fun u => (u.caller, u.callee)
  have h := Fren.Impls.PassEvidence.finite_application_closure marked (calls.map Prod.swap) (by trivial)
  simp only [fren_spec] at h ⊢
  have inverse : Fren.FinSet.ofList (calls.map Prod.swap) = (Fren.FinSet.ofList calls).inverse := by
    apply Fren.FinSet.ext
    intro p
    rcases p with ⟨a, b⟩
    simp only [Fren.FinSet.mem_ofList, Fren.FinSet.mem_inverse, List.mem_map]
    constructor
    · rintro ⟨p, hp, he⟩
      have : p = (b, a) := congrArg Prod.swap he
      exact this ▸ hp
    · intro hp
      exact ⟨(b, a), hp, rfl⟩
  have result := h.1.2
  rw [inverse] at result
  -- The spec imports and the runtime module choose different lawful instances.
  rw [matchingClosure_beq Auto.instBEqInt_auto (instBEqOfDecidableEq : BEq Int)] at result
  simpa [Fren.Core.groupInherited, marked, calls, List.map_map, Function.comp_def] using result

private theorem group_call_spec (ms : List Fren.Core.GroupParameter) (u : Fren.Core.GroupUse) :
    lang.group_call_decreases? (Fren.Seq.ofList (ms.map groupParameterOf)) (groupUseOf u) =
      Fren.Core.groupCallDecreases ms u := by
  apply Bool.eq_iff_iff.mpr
  by_cases hc : 0 ≤ u.caller ∧ u.caller < ms.length ∧ 0 ≤ u.callee ∧ u.callee < ms.length
  · have hcaller : u.caller.toNat < ms.length := by omega
    have hcallee : u.callee.toNat < ms.length := by omega
    by_cases ha : 0 ≤ ms[u.callee.toNat].decreasing ∧ ms[u.callee.toNat].decreasing < u.args.length
    · have harg : ms[u.callee.toNat].decreasing.toNat < u.args.length := by omega
      cases hf : u.form <;>
        simp [fren_spec, Fren.Core.groupCallDecreases, groupUseOf, recFormOf, groupParameterOf,
          Fren.Seq.nth, hc, hcaller, hcallee, ha, harg, hf]
    · cases hf : u.form <;>
        simp [fren_spec, Fren.Core.groupCallDecreases, groupUseOf, recFormOf, groupParameterOf,
          Fren.Seq.nth, hc, hcaller, hcallee, ha, hf]
  · simp [fren_spec, Fren.Core.groupCallDecreases, groupUseOf, recFormOf, Fren.Seq.nth, hc]
    intro _ h₀ h₁ h₂ h₃
    exact False.elim (hc ⟨h₀, h₁, h₂, h₃⟩)

private theorem position_used_spec (us : List Fren.Core.GroupUse) (i : Nat) :
    lang.group_position_used? (Fren.Seq.ofList (us.map groupUseOf)) i =
      Fren.Core.groupPositionUsed us i := by
  apply Bool.eq_iff_iff.mpr
  simp only [lang.group_position_used?, decide_eq_true_eq, Fren.Core.groupPositionUsed,
    List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨k, ⟨hk₀, hk₁⟩, h⟩
    have hk : k.toNat < us.length := by
      simp only [Fren.Seq.len_eq, Fren.Seq.toList_ofList, List.length_map] at hk₁
      omega
    refine ⟨us[k.toNat], List.getElem_mem _, ?_⟩
    rw [Fren.Seq.nth_of_lt _ _ hk₀ (by simpa using hk₁)] at h
    simpa [groupUseOf] using h
  · rintro ⟨u, hu, h⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
    refine ⟨k, ⟨by omega, by simpa using hk⟩, ?_⟩
    simpa [Fren.Seq.nth_of_lt, hk, groupUseOf] using h

impl group_search_positions: lang::group_search_positions
    for (n : Int) (us : List Fren.Core.GroupUse) (i : Nat) {
  count := n, uses := Fren.Seq.ofList (us.map groupUseOf), member := (i : Int),
  choices := (Fren.Core.groupPositionCount n us i : Int),
} by
  intro n us i _
  simp only [fren_spec, position_used_spec]
  by_cases hn : 0 < n <;> by_cases hu : Fren.Core.groupPositionUsed us i = true <;>
    simp_all [Fren.Core.groupPositionCount] <;> omega

impl group_search_prefix: lang::group_search_prefix
    for (ms : List Fren.Core.GroupParameter) (us : List Fren.Core.GroupUse) {
  members := Fren.Seq.ofList (ms.map groupParameterOf),
  uses := Fren.Seq.ofList (us.map groupUseOf),
  compatible? := Fren.Core.groupPrefixCompatible ms us,
} by
  intro ms us _
  change Fren.Core.groupPrefixCompatible ms us = true ↔ ∀ k : Int,
    0 ≤ k ∧ k < (Fren.Seq.ofList (us.map groupUseOf)).len →
      ((((Fren.Seq.ofList (us.map groupUseOf)).nth k).form = lang.RecForm.Applied ∧
        0 ≤ ((Fren.Seq.ofList (us.map groupUseOf)).nth k).caller) ∧
        0 ≤ ((Fren.Seq.ofList (us.map groupUseOf)).nth k).callee) ∧
      ((((Fren.Seq.ofList (us.map groupUseOf)).nth k).caller < (Fren.Seq.ofList (ms.map groupParameterOf)).len ∧
        ((Fren.Seq.ofList (us.map groupUseOf)).nth k).callee < (Fren.Seq.ofList (ms.map groupParameterOf)).len) →
        lang.group_call_decreases? (Fren.Seq.ofList (ms.map groupParameterOf))
          ((Fren.Seq.ofList (us.map groupUseOf)).nth k) = true)
  simp only [and_imp]
  have h := forall_seq_nth (us.map groupUseOf) (fun u =>
    ((u.form = lang.RecForm.Applied ∧ 0 ≤ u.caller) ∧ 0 ≤ u.callee) ∧
      (u.caller < (Fren.Seq.ofList (ms.map groupParameterOf)).len ∧
        u.callee < (Fren.Seq.ofList (ms.map groupParameterOf)).len →
        lang.group_call_decreases? (Fren.Seq.ofList (ms.map groupParameterOf)) u = true))
  simp only [and_imp] at h
  rw [h]
  simp only [Fren.Core.groupPrefixCompatible, List.all_eq_true, List.forall_mem_map]
  apply forall_congr'
  intro u
  apply imp_congr_right
  intro _
  rw [group_call_spec]
  by_cases hc : u.caller < ms.length <;> by_cases hd : u.callee < ms.length <;>
    cases hf : u.form <;> simp [groupUseOf, recFormOf, hc, hd, hf, and_assoc]

private theorem structural_group_spec (ms : List Fren.Core.GroupParameter) (us : List Fren.Core.GroupUse) :
    lang.group_structural? (Fren.Seq.ofList (ms.map groupParameterOf))
        (Fren.Seq.ofList (us.map groupUseOf)) = true ↔ Fren.Core.structuralGroup ms us = true := by
  simp only [lang.group_structural?, decide_eq_true_eq, and_imp]
  have hm := forall_seq_nth (ms.map groupParameterOf)
    (fun m => 0 ≤ m.decreasing ∧ m.decreasing < m.count)
  have hu := forall_seq_nth (us.map groupUseOf)
    (fun u => lang.group_call_decreases? (Fren.Seq.ofList (ms.map groupParameterOf)) u = true)
  simp only [lang.group_call_decreases?, decide_eq_true_eq] at hu
  rw [hm, hu]
  simp [Fren.Core.structuralGroup, List.all_eq_true, ← group_call_spec,
    lang.group_call_decreases?, groupParameterOf]

-- Over arbitrary finite groups, candidate positions and uses, including
-- malformed indices: the shared check computes descent from raw origins.
impl structural_group: lang::structural_group
    for (ms : List Fren.Core.GroupParameter) (us : List Fren.Core.GroupUse) {
  members := Fren.Seq.ofList (ms.map groupParameterOf),
  uses := Fren.Seq.ofList (us.map groupUseOf),
  accepted? := Fren.Core.structuralGroup ms us,
} by
  intro ms us _
  exact (structural_group_spec ms us).symm

/-- Candidate generation covers exactly all in-range choices for the given
parameter counts. In particular the search cannot silently miss a choice. -/
theorem mem_groupCandidates (ns : List Int) (ms : List Fren.Core.GroupParameter) :
    ms ∈ Fren.Core.groupCandidates ns ↔
      ms.map (·.count) = ns ∧ ∀ m ∈ ms, 0 ≤ m.decreasing ∧ m.decreasing < m.count := by
  induction ns generalizing ms with
  | nil => cases ms <;> simp [Fren.Core.groupCandidates]
  | cons n ns ih =>
    cases ms with
    | nil => simp [Fren.Core.groupCandidates]
    | cons m ms =>
      simp only [Fren.Core.groupCandidates, List.mem_flatMap, List.mem_range, List.mem_map,
        List.cons.injEq, ih, List.map_cons, List.forall_mem_cons]
      constructor
      · rintro ⟨i, hi, tail, ⟨ht, hp⟩, hm, rfl⟩
        subst hm
        refine ⟨by simp [ht], ?_, hp⟩
        change 0 ≤ (i : Int) ∧ (i : Int) < n
        omega
      · rintro ⟨⟨hm, ht⟩, h, hp⟩
        refine ⟨m.decreasing.toNat, by omega, ms, ⟨ht, hp⟩, ?_, rfl⟩
        cases m
        simp_all
        omega

section GroupSearch
open Fren.Core

private theorem get_middle [Inhabited α] (pre tail : List α) (a b : α) (i : Nat)
    (hi : i ≠ pre.length) :
    (pre ++ a :: tail)[i]! = (pre ++ b :: tail)[i]! := by
  simp only [List.getElem!_eq_getElem?_getD]
  by_cases h : i < pre.length
  · simp [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega : pre.length ≤ i),
      List.getElem?_append_right (by omega : pre.length ≤ i)]
    cases he : i - pre.length with
    | zero => omega
    | succ k => simp

private theorem call_middle (pre tail : List GroupParameter) (a b : GroupParameter) (u : GroupUse)
    (hc : u.caller ≠ (pre.length : Int)) (hd : u.callee ≠ (pre.length : Int)) :
    groupCallDecreases (pre ++ a :: tail) u = groupCallDecreases (pre ++ b :: tail) u := by
  unfold groupCallDecreases
  simp only [List.length_append, List.length_cons]
  split
  · rename_i h
    rw [get_middle pre tail a b u.caller.toNat (by omega),
      get_middle pre tail a b u.callee.toNat (by omega)]
  · rfl

private theorem structural_middle (pre tail : List GroupParameter) (n i j : Int) (us : List GroupUse)
    (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n)
    (hu : groupPositionUsed us pre.length = false) :
    structuralGroup (pre ++ { count := n, decreasing := i } :: tail) us =
      structuralGroup (pre ++ { count := n, decreasing := j } :: tail) us := by
  have unused : ∀ u ∈ us, u.caller ≠ (pre.length : Int) ∧ u.callee ≠ (pre.length : Int) := by
    simpa [groupPositionUsed, List.any_eq_false] using hu
  simp only [structuralGroup, List.all_append, List.all_cons, hi, hj]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor <;> intro h u mem
  · rw [← call_middle pre tail _ _ u (unused u mem).1 (unused u mem).2]
    exact h u mem
  · rw [call_middle pre tail _ _ u (unused u mem).1 (unused u mem).2]
    exact h u mem

private theorem call_append (pre tail : List GroupParameter) (u : GroupUse)
    (hc : 0 ≤ u.caller ∧ u.caller < pre.length)
    (hd : 0 ≤ u.callee ∧ u.callee < pre.length) :
    groupCallDecreases (pre ++ tail) u = groupCallDecreases pre u := by
  have hc' : u.caller.toNat < pre.length := by omega
  have hd' : u.callee.toNat < pre.length := by omega
  have hfull : 0 ≤ u.caller ∧ u.caller < (pre ++ tail).length ∧
      0 ≤ u.callee ∧ u.callee < (pre ++ tail).length := by simp only [List.length_append]; omega
  have hpre : 0 ≤ u.caller ∧ u.caller < pre.length ∧ 0 ≤ u.callee ∧ u.callee < pre.length := ⟨hc.1, hc.2, hd.1, hd.2⟩
  simp only [groupCallDecreases, if_pos hfull, if_pos hpre,
    List.getElem!_eq_getElem?_getD, List.getElem?_append_left hc', List.getElem?_append_left hd']


private theorem prefix_of_structural (pre tail : List GroupParameter) (us : List GroupUse)
    (h : structuralGroup (pre ++ tail) us = true) : groupPrefixCompatible pre us = true := by
  have h' := h
  simp only [structuralGroup, Bool.and_eq_true] at h'
  have hu := h'.2
  simp only [List.all_eq_true] at hu
  simp only [groupPrefixCompatible, List.all_eq_true]
  intro u mem
  have hc := hu u mem
  have hb : 0 ≤ u.caller ∧ u.caller < (pre ++ tail).length ∧
      0 ≤ u.callee ∧ u.callee < (pre ++ tail).length := by
    by_cases hb : 0 ≤ u.caller ∧ u.caller < (pre ++ tail).length ∧
        0 ≤ u.callee ∧ u.callee < (pre ++ tail).length
    · exact hb
    · simp only [groupCallDecreases, if_neg hb, Bool.false_eq_true] at hc
  have hf : u.form = .applied := by
    have hc' := hc
    simp only [groupCallDecreases, if_pos hb, Bool.and_eq_true, beq_iff_eq] at hc'
    exact hc'.1.1

  simp only [hf, BEq.rfl, hb.1, hb.2.2.1, and_self, decide_true, Bool.true_and]
  split
  · rename_i closed
    rw [← call_append pre tail u ⟨hb.1, closed.1⟩ ⟨hb.2.2.1, closed.2⟩]
    exact hc
  · rfl

private def refSearch (pre : List GroupParameter) (ns : List Int) (us : List GroupUse) :=
  ((groupCandidates ns).find? (fun tail => structuralGroup (pre ++ tail) us)).map (pre ++ ·)

private theorem refSearch_cons (pre : List GroupParameter) (n : Int) (ns : List Int) (us : List GroupUse) :
    refSearch pre (n :: ns) us = (List.range n.toNat).findSome? (fun i =>
      refSearch (pre ++ [{ count := n, decreasing := (i : Int) }]) ns us) := by
  simp [refSearch, groupCandidates, List.find?_flatMap, List.find?_map, List.map_findSome?,
    Function.comp_def, List.append_assoc]

private theorem refSearch_none (pre : List GroupParameter) (ns : List Int) (us : List GroupUse)
    (hp : groupPrefixCompatible pre us = false) : refSearch pre ns us = none := by
  have hnone : (groupCandidates ns).find? (fun tail => structuralGroup (pre ++ tail) us) = none := by
    apply List.find?_eq_none.mpr
    intro tail _
    cases hs : structuralGroup (pre ++ tail) us with
    | false => simp
    | true => have := prefix_of_structural pre tail us hs; simp [hp] at this
  simp [refSearch, hnone]

private theorem first_only {α : Type} (n : Nat) (f : Nat → Option α) (hn : 0 < n)
    (h : ∀ i ∈ List.range n, (f i).isSome = (f 0).isSome) :
    (List.range n).findSome? f = f 0 := by
  cases hf : f 0 with
  | none =>
    apply List.findSome?_eq_none_iff.mpr
    intro i hi
    have := h i hi
    simpa [hf] using this
  | some a =>
    cases n with
    | zero => omega
    | succ n => simp [List.range_succ_eq_map, hf]

theorem groupSearch_eq (pre : List GroupParameter) (ns : List Int) (us : List GroupUse) :
    groupSearch us pre ns = refSearch pre ns us := by
  induction ns generalizing pre with
  | nil => simp [groupSearch, refSearch, groupCandidates]
  | cons n ns ih =>
    by_cases hp : groupPrefixCompatible pre us = true
    · rw [groupSearch, if_pos hp, refSearch_cons]
      simp only [groupPositionCount]
      by_cases hu : groupPositionUsed us pre.length = true
      · simp only [hu, ↓reduceIte]
        congr 1
        funext i
        exact ih _
      · have hu' : groupPositionUsed us pre.length = false := by simpa using hu
        simp only [hu', Bool.false_eq_true, ↓reduceIte]
        by_cases hn : 0 < n
        · simp only [hn, ↓reduceIte, List.range_one, List.findSome?_cons, List.findSome?_nil, ih]
          have hsame (i : Nat) (hi : i ∈ List.range n.toNat) :
              (refSearch (pre ++ [{ count := n, decreasing := (i : Int) }]) ns us).isSome =
                (refSearch (pre ++ [{ count := n, decreasing := 0 }]) ns us).isSome := by
            simp only [refSearch, Option.isSome_map, List.isSome_find?]
            apply List.any_congr rfl
            intro tail
            simpa only [List.append_assoc, List.singleton_append] using
              structural_middle pre tail n i 0 us ⟨by omega, by simpa using hi⟩ ⟨by omega, hn⟩ hu'
          rw [first_only n.toNat _ (by omega) hsame]
          cases refSearch (pre ++ [{ count := n, decreasing := 0 }]) ns us <;> rfl
        · have hz : n.toNat = 0 := by omega
          simp [hn, hz]
    · have hp' : groupPrefixCompatible pre us = false := by simpa using hp
      rw [groupSearch, if_neg hp]
      exact (refSearch_none pre (n :: ns) us hp').symm

theorem recursionGroup_eq (ns : List Int) (us : List GroupUse) :
    recursionGroup ns us = (groupCandidates ns).find? (structuralGroup · us) := by
  have hsearch := groupSearch_eq [] ns us
  simp [refSearch] at hsearch
  unfold recursionGroup
  split
  · exact hsearch
  · rename_i invalid
    symm
    apply List.find?_eq_none.mpr
    intro ms mem hs
    obtain ⟨counts, bounds⟩ := (mem_groupCandidates ns ms).mp mem
    have hpos : ns.all (fun n => decide (0 < n)) = true := by
      rw [← counts]
      simp only [List.all_map, List.all_eq_true, decide_eq_true_eq, Function.comp_def]
      intro m hm
      have := bounds m hm
      omega
    have hlen : ms.length = ns.length := by simpa using congrArg List.length counts
    have hu : us.all (fun u => decide (0 ≤ u.caller ∧ u.caller < ns.length ∧
        0 ≤ u.callee ∧ u.callee < ns.length)) = true := by
      have hs' := hs
      simp only [structuralGroup, Bool.and_eq_true, List.all_eq_true] at hs'
      simp only [List.all_eq_true, decide_eq_true_eq]
      intro u mem
      have hc := hs'.2 u mem
      unfold groupCallDecreases at hc
      split at hc
      · rename_i h
        simpa [hlen] using h
      · contradiction
    simp only [hpos, hu, Bool.and_self] at invalid
    exact invalid trivial

end GroupSearch

/-- The group search succeeds exactly when some choice of the members'
parameters passes the specified structural judgment. -/
theorem recursionGroup_exists (ns : List Int) (us : List Fren.Core.GroupUse) :
    (Fren.Core.recursionGroup ns us).isSome = true ↔
      ∃ ms, ms.map (·.count) = ns ∧ Fren.Core.structuralGroup ms us = true := by
  rw [recursionGroup_eq]
  simp only [List.isSome_find?, List.any_eq_true, mem_groupCandidates]
  constructor
  · rintro ⟨ms, ⟨hc, _⟩, h⟩
    exact ⟨ms, hc, h⟩
  · rintro ⟨ms, hc, h⟩
    have hb := h
    simp only [Fren.Core.structuralGroup, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hb
    exact ⟨ms, ⟨hc, hb.1⟩, h⟩

/-- A returned selection has the requested signature and passes the
judgment bound to the requirement, not merely some other candidate. -/
theorem recursionGroup_some {ns : List Int} {us : List Fren.Core.GroupUse}
    {ms : List Fren.Core.GroupParameter} (h : Fren.Core.recursionGroup ns us = some ms) :
    ms.map (·.count) = ns ∧ Fren.Core.structuralGroup ms us = true := by
  rw [recursionGroup_eq] at h
  exact ⟨((mem_groupCandidates ns ms).mp (List.mem_of_find?_eq_some h)).1,
    List.find?_some (p := fun xs => Fren.Core.structuralGroup xs us) h⟩

private theorem group_counts_spec (ns : List Int) (ms : List Fren.Core.GroupParameter) :
    lang.group_counts_match? (Fren.Seq.ofList ns) (Fren.Seq.ofList (ms.map groupParameterOf)) = true ↔
      ms.map (·.count) = ns := by
  simp only [lang.group_counts_match?, decide_eq_true_eq, Fren.Seq.len_eq, Fren.Seq.toList_ofList,
    List.length_map]
  constructor
  · rintro ⟨hl, h⟩
    apply List.ext_getElem (by simp only [List.length_map]; omega)
    intro i hi hn
    have := h i ⟨by omega, by simpa using hn⟩
    simpa [Fren.Seq.nth_of_lt, hn, show i < ms.length by simpa using hi, groupParameterOf] using this
  · intro h
    have hl : ns.length = ms.length := by simpa using (congrArg List.length h).symm
    refine ⟨by omega, ?_⟩
    intro i hi
    have hn : i.toNat < ns.length := by omega
    have hm : i.toNat < ms.length := by omega
    have he := congrArg (fun xs => xs[i.toNat]?) h
    have hms : (Fren.Seq.ofList (ms.map groupParameterOf)).nth i = groupParameterOf ms[i.toNat] := by
      simp [Fren.Seq.nth, hi.1, show i < (ms.length : Int) by omega]
    have hns : (Fren.Seq.ofList ns).nth i = ns[i.toNat] := by
      simp [Fren.Seq.nth, hi.1, hi.2]
    rw [hms, hns]
    simpa [hm, hn, groupParameterOf] using he

private def fromGroupParameter (m : lang.GroupParameter) : Fren.Core.GroupParameter :=
  { count := m.count, decreasing := m.decreasing }

private theorem groupParameter_roundtrip (ms : Fren.Seq lang.GroupParameter) :
    Fren.Seq.ofList ((ms.toList.map fromGroupParameter).map groupParameterOf) = ms := by
  apply Fren.Seq.ext
  simp only [Fren.Seq.toList_ofList, List.map_map]
  have hi : groupParameterOf ∘ fromGroupParameter = id := by
    funext m
    cases m
    rfl
  simp [hi]

-- The inferred decision is specified too: no caller supplies a precomputed
-- fact that a suitable choice of decreasing positions exists.
impl structural_group_search: lang::structural_group_search
    for (ns : List Int) (us : List Fren.Core.GroupUse) {
  counts := Fren.Seq.ofList ns,
  uses := Fren.Seq.ofList (us.map groupUseOf),
  found? := (Fren.Core.recursionGroup ns us).isSome,
} by
  intro ns us _
  change (Fren.Core.recursionGroup ns us).isSome = true ↔
    ∃ ms : Fren.Seq lang.GroupParameter,
      lang.group_counts_match? (Fren.Seq.ofList ns) ms = true ∧
      lang.group_structural? ms (Fren.Seq.ofList (us.map groupUseOf)) = true
  rw [recursionGroup_exists]
  constructor
  · rintro ⟨ms, hc, hs⟩
    exact ⟨Fren.Seq.ofList (ms.map groupParameterOf), (group_counts_spec ns ms).mpr hc,
      (structural_group_spec ms us).mpr hs⟩
  · rintro ⟨ms, hc, hs⟩
    have hr := groupParameter_roundtrip ms
    refine ⟨ms.toList.map fromGroupParameter, (group_counts_spec ns _).mp ?_,
      (structural_group_spec _ us).mp ?_⟩
    · simpa only [hr] using hc
    · simpa only [hr] using hs

private theorem inGroup_decreases (u : Fren.Core.RecUse) (n i : Nat) :
    Fren.Core.groupCallDecreases [{ count := n, decreasing := i }] u.inGroup =
      u.decreasesAt i := by
  apply Bool.eq_iff_iff.mpr
  by_cases hi : i < u.args.length
  · cases hf : u.form <;>
      simp [Fren.Core.groupCallDecreases, Fren.Core.RecUse.inGroup, Fren.Core.RecUse.decreasesAt,
        hf, hi, getElem!_pos]
    all_goals cases u.args[i] <;> simp
  · simp [Fren.Core.groupCallDecreases, Fren.Core.RecUse.inGroup, Fren.Core.RecUse.decreasesAt,
      hi]

private theorem singleton_structural (uses : List Fren.Core.RecUse) (n i : Nat) (hi : i < n) :
    Fren.Core.structuralGroup [{ count := n, decreasing := i }] (uses.map Fren.Core.RecUse.inGroup) =
      (Fren.Core.firstFailure uses i).isNone := by
  apply Bool.eq_iff_iff.mpr
  simp [Fren.Core.structuralGroup, Fren.Core.firstFailure, List.all_eq_true,
    inGroup_decreases, hi]

/-- The singleton adapter preserves the entire previous classifier for all
parameter counts and uses, including malformed arities and diagnostics.
This also proves that the group's first-choice order preserves the first
successful self-recursion parameter. -/
theorem selfRecursion_eq (n : Nat) (uses : List Fren.Core.RecUse) :
    Fren.Core.selfRecursion n uses =
      (if uses.isEmpty then .notRecursive
       else match (List.range n).find? (Fren.Core.firstFailure uses · |>.isNone) with
         | some i => .structural i
         | none =>
           let fs := (List.range n).map fun i => (Fren.Core.firstFailure uses i).getD 0
           let k := fs.foldl max 0
           .notStructural k (fs.idxOf k)) := by
  have hc : Fren.Core.groupCandidates [n] =
      (List.range n).map (fun i => [{ count := (n : Int), decreasing := (i : Int) }]) := by
    simp [Fren.Core.groupCandidates, ← List.map_eq_flatMap]
  have hf : (List.range n).find? (fun (i : Nat) =>
      Fren.Core.structuralGroup [{ count := n, decreasing := i }] (uses.map Fren.Core.RecUse.inGroup)) =
        (List.range n).find? (Fren.Core.firstFailure uses · |>.isNone) := by
    rw [← List.head?_filter, ← List.head?_filter]
    congr 1
    exact List.filter_congr (fun i hi => singleton_structural uses n i (List.mem_range.mp hi))
  simp only [Fren.Core.selfRecursion, recursionGroup_eq, hc, List.find?_map, Function.comp_def]
  rw [hf]
  cases (List.range n).find? (Fren.Core.firstFailure uses · |>.isNone) <;> rfl

end Fren.Impls
