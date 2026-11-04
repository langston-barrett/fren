-- keep-sorted start
import FrenCore.Recursion
import Reqs.Lang
-- keep-sorted end

open Fren.Lang

namespace Fren.Impls

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
    (∀ k : Int, 0 ≤ k ∧ k < (Fren.Seq.ofList xs).len → P ((Fren.Seq.ofList xs).nth k)) ↔
      ∀ x ∈ xs, P x := by
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simpa [Fren.Seq.nth_of_lt, hi] using h i ⟨by omega, by simpa using hi⟩
  · intro h k hk
    rw [Fren.Seq.nth_of_lt _ _ hk.1 (by simpa using hk.2)]
    exact h _ (List.getElem_mem _)

private theorem group_call_spec (ms : List Fren.Core.GroupParameter) (u : Fren.Core.GroupUse) :
    lang.group_call_decreases? (Fren.Seq.ofList (ms.map groupParameterOf)) (groupUseOf u) =
      Fren.Core.groupCallDecreases ms u := by
  by_cases hc : 0 ≤ u.caller ∧ u.caller < ms.length ∧ 0 ≤ u.callee ∧ u.callee < ms.length
  · have hcaller : u.caller.toNat < ms.length := by omega
    have hcallee : u.callee.toNat < ms.length := by omega
    by_cases ha : 0 ≤ ms[u.callee.toNat].decreasing ∧ ms[u.callee.toNat].decreasing < u.args.length
    · have harg : ms[u.callee.toNat].decreasing.toNat < u.args.length := by omega
      cases u.form <;>
        simp [fren_spec, Fren.Core.groupCallDecreases, groupUseOf, recFormOf, groupParameterOf,
          Fren.Seq.nth, hc, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hcaller, hcallee, ha, harg]
    · cases u.form <;>
        simp [fren_spec, Fren.Core.groupCallDecreases, groupUseOf, recFormOf, groupParameterOf,
          Fren.Seq.nth, hc, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hcaller, hcallee, ha]
  · cases u.form <;>
      simp [fren_spec, Fren.Core.groupCallDecreases, groupUseOf, recFormOf, Fren.Seq.nth, hc]

private theorem structural_group_spec (ms : List Fren.Core.GroupParameter) (us : List Fren.Core.GroupUse) :
    lang.group_structural? (Fren.Seq.ofList (ms.map groupParameterOf))
        (Fren.Seq.ofList (us.map groupUseOf)) = true ↔ Fren.Core.structuralGroup ms us = true := by
  simp only [lang.group_structural?, decide_eq_true_eq, forall_seq_nth, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  simp [Fren.Core.structuralGroup, List.all_eq_true, groupParameterOf, group_call_spec]

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
        exact ⟨by simp [ht], by constructor; · omega; · exact hp⟩
      · rintro ⟨⟨hm, ht⟩, h, hp⟩
        refine ⟨m.decreasing.toNat, by omega, ms, ⟨ht, hp⟩, ?_, rfl⟩
        cases m
        simp_all

/-- The group search succeeds exactly when some choice of the members'
parameters passes the specified structural judgment. -/
theorem recursionGroup_exists (ns : List Int) (us : List Fren.Core.GroupUse) :
    (Fren.Core.recursionGroup ns us).isSome = true ↔
      ∃ ms, ms.map (·.count) = ns ∧ Fren.Core.structuralGroup ms us = true := by
  simp only [Fren.Core.recursionGroup, List.isSome_find?, List.any_eq_true, mem_groupCandidates]
  constructor
  · rintro ⟨ms, ⟨hc, _⟩, h⟩
    exact ⟨ms, hc, h⟩
  · rintro ⟨ms, hc, h⟩
    have hb : ∀ m ∈ ms, 0 ≤ m.decreasing ∧ m.decreasing < m.count := by
      simpa [Fren.Core.structuralGroup, List.all_eq_true] using (Bool.and_eq_true.mp h).1
    exact ⟨ms, ⟨hc, hb⟩, h⟩

/-- A returned selection has the requested signature and passes the
judgment bound to the requirement, not merely some other candidate. -/
theorem recursionGroup_some {ns : List Int} {us : List Fren.Core.GroupUse}
    {ms : List Fren.Core.GroupParameter} (h : Fren.Core.recursionGroup ns us = some ms) :
    ms.map (·.count) = ns ∧ Fren.Core.structuralGroup ms us = true :=
  ⟨((mem_groupCandidates ns ms).mp (List.mem_of_find?_eq_some h)).1, List.find?_some h⟩

private theorem group_counts_spec (ns : List Int) (ms : List Fren.Core.GroupParameter) :
    lang.group_counts_match? (Fren.Seq.ofList ns) (Fren.Seq.ofList (ms.map groupParameterOf)) = true ↔
      ms.map (·.count) = ns := by
  simp only [lang.group_counts_match?, decide_eq_true_eq, Fren.Seq.len_eq, Fren.Seq.toList_ofList,
    List.length_map]
  constructor
  · rintro ⟨hl, h⟩
    apply List.ext_getElem (by simpa using hl.symm)
    intro i hi hn
    have := h i ⟨by omega, by simpa using hn⟩
    simpa [Fren.Seq.nth_of_lt, hn, show i < ms.length by simpa using hi, groupParameterOf] using this
  · intro h
    have hl : ns.length = ms.length := by simpa using (congrArg List.length h).symm
    refine ⟨hl, ?_⟩
    intro i hi
    have hn : i.toNat < ns.length := by omega
    have hm : i.toNat < ms.length := by omega
    have he := congrArg (fun xs => xs[i.toNat]?) h
    simpa [Fren.Seq.nth_of_lt, hi.1, hi.2, hn, hm, groupParameterOf] using he

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

end Fren.Impls
