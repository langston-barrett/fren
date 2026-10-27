-- keep-sorted start
import FrenCore.SeqElems
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # Quantifiers over elements (`Reqs/Lang/ElementQuantifiers`) -/

namespace Fren.Impls

def toElementUse : Fren.Core.ElementUse → lang.ElementUse
  | .value => .Value
  | .index => .Index
  | .seqArgument => .SeqArgument
  | .receiver => .Receiver
  | .factArgument => .FactArgument

theorem toElementUse_inj (a b : Fren.Core.ElementUse) : toElementUse a = toElementUse b ↔ a = b := by
  cases a <;> cases b <;> simp [toElementUse]

def toElementMembers : Fren.Core.ElementMembers → lang.ElementMembers
  | .seq => .Sequence
  | .set => .SetOrRelation
  | .none => .Neither

def toElementBinder (b : Fren.Core.ElementBinder) : lang.ElementBinder :=
  { members := toElementMembers b.members, «receiver_bound?» := b.receiverBound
    «receiver_output?» := b.receiverOutput, uses := Fren.FinSet.ofList (b.uses.map toElementUse) }

def toElementNesting : Fren.Core.ElementNesting → lang.ElementNesting
  | .top => .Top
  | .direct => .Direct
  | .other => .Other

def toElementVerdict : Fren.Core.ElementVerdict → lang.ElementVerdict
  | .inCore => .InCore
  | .notMembers => .NotMembers
  | .setMembers => .SetMembers
  | .receiverBound => .ReceiverBound
  | .receiverOutput => .ReceiverOutput
  | .used u => .Used (toElementUse u)
  | .nested => .Nested

theorem toElementVerdict_inCore (v : Fren.Core.ElementVerdict) :
    toElementVerdict v = .InCore ↔ v.isInCore = true := by
  cases v <;> simp [toElementVerdict, Fren.Core.ElementVerdict.isInCore]

theorem mem_uses (b : Fren.Core.ElementBinder) (u : Fren.Core.ElementUse) :
    toElementUse u ∈ (toElementBinder b).uses ↔ u ∈ b.uses := by
  simp only [toElementBinder, Fren.FinSet.mem_ofList, List.mem_map, toElementUse_inj]
  exact ⟨fun ⟨_, h, e⟩ => e ▸ h, fun h => ⟨u, h, rfl⟩⟩

/-- The spec's verdict of a bound name is the code's. -/
theorem binder_verdict_eq (b : Fren.Core.ElementBinder) :
    lang.binder_verdict (toElementBinder b) = toElementVerdict b.verdict := by
  have hi := mem_uses b .index
  have hs := mem_uses b .seqArgument
  have hr := mem_uses b .receiver
  have hf := mem_uses b .factArgument
  simp only [toElementUse] at hi hs hr hf
  unfold lang.binder_verdict
  simp only [hi, hs, hr, hf]
  unfold Fren.Core.ElementBinder.verdict
  cases hm : b.members
  · cases hb : b.receiverBound <;> cases ho : b.receiverOutput <;>
      by_cases c1 : Fren.Core.ElementUse.index ∈ b.uses <;> by_cases c2 : Fren.Core.ElementUse.seqArgument ∈ b.uses <;>
      by_cases c3 : Fren.Core.ElementUse.receiver ∈ b.uses <;> by_cases c4 : Fren.Core.ElementUse.factArgument ∈ b.uses <;>
      simp [toElementBinder, toElementMembers, hm, hb, ho, c1, c2, c3, c4, Fren.Core.ElementUse.outside, List.find?,
        toElementVerdict, toElementUse]
  all_goals simp [toElementBinder, toElementMembers, hm, toElementVerdict]

-- For every list of bound names and every nesting: the verdict that both
-- front ends decide by. That each reads its syntax into the right bound
-- names is not proved here, but tested by both on the same ui tests.
impl element_quantifier: lang::element_quantifier for (bs : List Fren.Core.ElementBinder) (n : Fren.Core.ElementNesting) {
  binders := Fren.Seq.ofList (bs.map toElementBinder),
  nesting := toElementNesting n,
  verdict := toElementVerdict (Fren.Core.elementVerdict n bs),
} by
  intro bs n _
  simp only [fren_spec]
  have bv := binder_verdict_eq
  unfold lang.binder_verdict at bv
  have nth (j : Nat) (h : j < bs.length) :
      (Fren.Seq.ofList (bs.map toElementBinder)).nth (j : Int) = toElementBinder bs[j] := by
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using h)]; simp
  refine ⟨?_, ?_⟩
  · intro j ⟨⟨⟨h0, hj⟩, hne⟩, hbefore⟩
    have hj' : j.toNat < bs.length := by simp at hj; omega
    have hjj : j = ((j.toNat : Nat) : Int) := by omega
    rw [hjj, nth _ hj', bv] at hne ⊢
    have hfind : bs.find? (!·.verdict.isInCore) = some bs[j.toNat] := by
      rw [List.find?_eq_some_iff_getElem]
      refine ⟨by simpa [toElementVerdict_inCore] using hne, j.toNat, hj', rfl, fun i hi => ?_⟩
      have := hbefore i ⟨by omega, by omega⟩
      rw [nth i (by omega), bv, toElementVerdict_inCore] at this
      simp [this]
    simp [Fren.Core.elementVerdict, hfind]
  · intro hall
    have hfind : bs.find? (!·.verdict.isInCore) = none := by
      rw [List.find?_eq_none]
      intro b hb
      have := hall (toElementBinder b) (by simp only [Fren.Seq.mem_iff, Fren.Seq.toList_ofList, List.mem_map]; exact ⟨b, hb, rfl⟩)
      rw [bv, toElementVerdict_inCore] at this
      simp [this]
    cases n <;> simp [Fren.Core.elementVerdict, hfind, toElementNesting, toElementVerdict]

interp lang::IndexTerm := Int

-- For every query's sources, here over integers, by the function that both
-- front ends call (`Fren.Core.indexSet`), which is generic in the terms:
-- the binary's SMT-LIB terms and the Lean-hosted front end's Lean terms.
impl index_set: lang::index_set for (s : Fren.Core.IndexSources Int) {
  zero := s.zero,
  lasts := Fren.Seq.ofList s.lasts,
  reads := Fren.Seq.ofList s.reads,
  positions := Fren.Seq.ofList (s.updates.map (·.2.1)),
  before := Fren.Seq.ofList (s.updates.map (·.1)),
  after := Fren.Seq.ofList (s.updates.map (·.2.2)),
  witnesses := Fren.Seq.ofList s.witnesses,
  terms := Fren.Seq.ofList (Fren.Core.indexSet s),
  «index_set?» := true,
} by
  intro s _
  simp only [fren_spec, true_iff]
  have mem (t : Int) : t ∈ Fren.Core.indexSet s ↔ t = s.zero ∨ t ∈ s.lasts ∨ t ∈ s.reads ∨
      (∃ u ∈ s.updates, t = u.1 ∨ t = u.2.1 ∨ t = u.2.2) ∨ t ∈ s.witnesses := by
    rw [Fren.Core.mem_indexSet]
    simp only [Fren.Core.IndexSources.candidates, List.mem_cons, List.mem_append, List.mem_flatMap,
      List.not_mem_nil, or_false, or_assoc]
  obtain ⟨r, hr⟩ := Fren.Core.indexSet_head s
  have nth (l : List Int) (i : Nat) (h : i < l.length) : (Fren.Seq.ofList l).nth (i : Int) = l[i] := by
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using h)]; simp
  have upd (u : Int × Int × Int) (hu : u ∈ s.updates) : u.1 ∈ Fren.Core.indexSet s ∧ u.2.1 ∈ Fren.Core.indexSet s ∧
      u.2.2 ∈ Fren.Core.indexSet s :=
    ⟨(mem _).mpr (.inr (.inr (.inr (.inl ⟨u, hu, .inl rfl⟩)))), (mem _).mpr (.inr (.inr (.inr (.inl ⟨u, hu, .inr (.inl rfl)⟩)))),
      (mem _).mpr (.inr (.inr (.inr (.inl ⟨u, hu, .inr (.inr rfl)⟩))))⟩
  simp only [Fren.Seq.mem_iff, Fren.Seq.toList_ofList]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp [hr, Fren.Seq.ext_iff]
  · rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, nth _ 0 (by simp [hr])]; simp [hr]
  · intro t ht; exact (mem t).mpr (.inr (.inl ht))
  · intro t ht; exact (mem t).mpr (.inr (.inr (.inl ht)))
  · intro i ⟨h0, hi⟩
    have hi' : i.toNat < s.updates.length := by simp at hi; omega
    have hii : i = ((i.toNat : Nat) : Int) := by omega
    rw [hii, nth _ _ (by simpa using hi'), nth _ _ (by simpa using hi'), nth _ _ (by simpa using hi')]
    simp only [List.getElem_map]
    have := upd _ (List.getElem_mem hi')
    exact ⟨⟨this.1, this.2.1⟩, this.2.2⟩
  · intro t ht; exact (mem t).mpr (.inr (.inr (.inr (.inr ht))))
  · intro t ht
    rcases (mem t).mp ht with h | h | h | ⟨u, hu, hm⟩ | h
    · exact .inl (.inl (.inl (.inl (.inl (.inl h)))))
    · exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
    · exact .inl (.inl (.inl (.inl (.inr h))))
    · rcases hm with e | e | e <;> subst e
      · exact .inl (.inl (.inr (List.mem_map_of_mem hu)))
      · exact .inl (.inl (.inl (.inr (List.mem_map_of_mem hu))))
      · exact .inl (.inr (List.mem_map_of_mem hu))
    · exact .inr h
  · intro i j ⟨⟨h0, hij⟩, hj⟩ he
    have nd := Fren.Core.nodup_indexSet s
    have hj' : j.toNat < (Fren.Core.indexSet s).length := by simp at hj; omega
    have hii : i = ((i.toNat : Nat) : Int) := by omega
    have hjj : j = ((j.toNat : Nat) : Int) := by omega
    rw [hii, hjj, nth _ _ (by omega), nth _ _ hj'] at he
    have := (List.getElem_inj nd).mp he
    omega

-- For every sequence, values of the index set and set of elements at which
-- the body holds: the projection, by which a model of an expansion is made
-- one of the quantified query (`Fren.Core.project`).
impl element_projection: lang::element_projection for (q ix : List Int) (good : Fren.FinSet Int) (i v : Int) {
  q := Fren.Seq.ofList q,
  ix := Fren.Seq.ofList ix,
  good := good,
  i := i,
  v := v,
  projected := Fren.Seq.ofList (Fren.Core.project ix q),
  updated := Fren.Seq.ofList (Fren.Core.project ix (Fren.Seq.update (Fren.Seq.ofList q) i v).toList),
  «projection?» := true,
} by
  intro q ix good i v h0
  simp only [fren_spec, true_iff] at h0 ⊢
  have h0' : (0 : Int) ∈ ix := by simpa [Fren.Seq.mem_iff] using h0
  refine ⟨⟨⟨by simp, ?_⟩, ?_⟩, ?_⟩
  · intro t ⟨ht, h1, h2⟩
    have ht' : ((t.toNat : Nat) : Int) ∈ ix := by rw [Int.toNat_of_nonneg h1]; simpa [Fren.Seq.mem_iff] using ht
    have h2' : t.toNat < q.length := by simp at h2; omega
    rw [Fren.Seq.nth_of_lt _ _ h1 (by simp; omega), Fren.Seq.nth_of_lt _ _ h1 (by simp; omega)]
    simp only [Fren.Seq.toList_ofList]
    exact Fren.Core.project_read ix q t.toNat ht' h2'
  · intro hI x hx
    simp only [Fren.Seq.mem_iff, Fren.Seq.toList_ofList] at hx
    refine Fren.Core.project_all ix q (· ∈ good) h0' (fun t ht hlt => ?_) x hx
    have := hI t ⟨by simpa [Fren.Seq.mem_iff] using ht, by omega, by simpa using hlt⟩
    rwa [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using hlt)] at this
  · intro ⟨⟨hi, hs⟩, h1, h2⟩
    have hlt : i.toNat < q.length := by simp at h2; omega
    have hi' : ((i.toNat : Nat) : Int) ∈ ix := by rw [Int.toNat_of_nonneg h1]; simpa [Fren.Seq.mem_iff] using hi
    have hs' : ((i.toNat : Nat) : Int) + 1 ∈ ix := by rw [Int.toNat_of_nonneg h1]; simpa [Fren.Seq.mem_iff] using hs
    apply Fren.Seq.ext
    rw [Fren.Seq.toList_update_of_lt _ _ _ h1 (by simpa using h2), Fren.Seq.toList_update_of_lt _ _ _ h1 (by simp; omega)]
    simp only [Fren.Seq.toList_ofList]
    exact Fren.Core.project_set ix q i.toNat v hi' hs'

-- For every sequence and set of elements: the two meanings of a quantifier
-- over elements, by the elements and by the positions.
impl element_meaning: lang::element_meaning for (q : List Int) (good : Fren.FinSet Int) {
  q := Fren.Seq.ofList q,
  good := good,
  holds? := q.all (· ∈ good),
} by
  intro q good _
  simp only [fren_spec]
  refine ⟨?_, ?_⟩
  · simp [Fren.Seq.mem_iff, List.all_eq_true]
  · simp only [List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro h i ⟨h0, hi⟩
      rw [Fren.Seq.nth_of_lt _ _ h0 hi]
      exact h _ (List.getElem_mem _)
    · intro h x hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      have := h j ⟨by omega, by simpa using hj⟩
      rwa [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using hj)] at this

-- For every number of instances: the limit that both front ends apply.
impl element_size: lang::element_size for (n : Nat) {
  n_instances := n,
  accepted? := Fren.Core.elementSizeAccepted n,
} by
  intro n _
  simp only [fren_spec, Fren.Core.elementSizeAccepted, Fren.Core.maxElementInstances, decide_eq_true_eq]
  omega

end Fren.Impls
