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
  | .quantifiedArgument => .QuantifiedArgument

theorem toElementUse_inj (a b : Fren.Core.ElementUse) : toElementUse a = toElementUse b ↔ a = b := by
  cases a <;> cases b <;> simp [toElementUse]

def toElementMembers : Fren.Core.ElementMembers → lang.ElementMembers
  | .seq => .Sequence
  | .set => .SetOrRelation
  | .none => .Neither

def toElementBinder (b : Fren.Core.ElementBinder) : lang.ElementBinder :=
  { members := toElementMembers b.members, «receiver_bound?» := b.receiverBound
    uses := Fren.FinSet.ofList (b.uses.map toElementUse) }

def toElementNesting : Fren.Core.ElementNesting → lang.ElementNesting
  | .top => .Top
  | .direct => .Direct
  | .other => .Other

def toElementVerdict : Fren.Core.ElementVerdict → lang.ElementVerdict
  | .inCore => .InCore
  | .notMembers => .NotMembers
  | .setMembers => .SetMembers
  | .receiverBound => .ReceiverBound
  | .mentionsOutput => .MentionsOutput
  | .mentionsBound => .MentionsBound
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
  have hq := mem_uses b .quantifiedArgument
  simp only [toElementUse] at hi hs hr hf hq
  unfold lang.binder_verdict
  simp only [hi, hs, hr, hf, hq]
  unfold Fren.Core.ElementBinder.verdict
  cases hm : b.members
  · cases hb : b.receiverBound
    · by_cases c1 : Fren.Core.ElementUse.index ∈ b.uses <;> by_cases c2 : Fren.Core.ElementUse.seqArgument ∈ b.uses <;>
        by_cases c3 : Fren.Core.ElementUse.receiver ∈ b.uses <;> by_cases c4 : Fren.Core.ElementUse.factArgument ∈ b.uses <;>
        by_cases c5 : Fren.Core.ElementUse.quantifiedArgument ∈ b.uses <;>
        simp [toElementBinder, toElementMembers, hm, hb, c1, c2, c3, c4, c5, Fren.Core.ElementUse.outside, List.find?,
          toElementVerdict, toElementUse]
    · simp [toElementBinder, toElementMembers, hm, hb, toElementVerdict]
  all_goals simp [toElementBinder, toElementMembers, hm, toElementVerdict]

-- For every list of bound names and every nesting: the verdict that both
-- front ends decide by. That each reads its syntax into the right bound
-- names is not proved here, but tested by both on the same ui tests.
impl element_quantifier: lang::element_quantifier for (bs : List Fren.Core.ElementBinder) (n : Fren.Core.ElementNesting)
    (o b : Bool) {
  binders := Fren.Seq.ofList (bs.map toElementBinder),
  nesting := toElementNesting n,
  «output?» := o,
  «bound?» := b,
  verdict := toElementVerdict (Fren.Core.elementVerdict n o b bs),
} by
  intro bs n o b _
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
    cases n <;> cases o <;> cases b <;> simp [Fren.Core.elementVerdict, hfind, toElementNesting, toElementVerdict]

def toFrame : Fren.Core.Frame → lang.Frame
  | .element all spine => .Element all spine
  | .other => .Other

theorem toFrame_eq (f : Fren.Core.Frame) (all : Bool) : toFrame f = .Element all true ↔ f = .element all true := by
  cases f <;> simp [toFrame]

theorem inChain_iff (fs : List Fren.Core.Frame) (all : Bool) (j : Nat) :
    Fren.Core.inChain fs all j = true ↔ ∀ k : Nat, j ≤ k → (h : k < fs.length) → fs[k] = .element all true := by
  unfold Fren.Core.inChain
  rw [List.all_eq_true]
  constructor
  · intro h k hjk hk
    have := h ((fs.drop j)[k - j]'(by simp; omega)) (List.getElem_mem _)
    simp only [List.getElem_drop, beq_iff_eq] at this
    have e : j + (k - j) = k := by omega
    simp only [e] at this
    exact this
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.length_drop] at hi
    simp only [List.getElem_drop, beq_iff_eq]
    exact h (j + i) (by omega) (by omega)

-- For every list of binders around a quantifier and every set of them that
-- its body mentions: which quantifiers both front ends expand
-- (`Fren.Core.siteExpanded`). That each reads its query into the right
-- binders is not proved here, but tested by both on the same ui tests.
impl site_expanded: lang::site_expanded for (fs : List Fren.Core.Frame) (all rc : Bool) (ms : List Nat) {
  frames := Fren.Seq.ofList (fs.map toFrame),
  «all?» := all,
  «receivers_closed?» := rc,
  mentioned := Fren.Seq.ofList (ms.map fun m : Nat => (m : Int)),
  «expanded?» := Fren.Core.siteExpanded fs all rc ms,
} by
  intro fs all rc ms _
  simp only [fren_spec]
  have nth (k : Nat) (h : k < fs.length) : (Fren.Seq.ofList (fs.map toFrame)).nth (k : Int) = toFrame fs[k] := by
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using h)]; simp
  unfold Fren.Core.siteExpanded
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Fren.Seq.mem_iff, Fren.Seq.toList_ofList,
    List.mem_map, Fren.Seq.len_eq, List.length_map]
  refine and_congr Iff.rfl ⟨fun h j ⟨m, hm, e⟩ => ?_, fun h m hm => ?_⟩
  · subst e
    obtain ⟨hlt, hc⟩ := h m hm
    refine ⟨⟨by omega, by omega⟩, fun k ⟨_, _⟩ => ?_⟩
    have hk : k.toNat < fs.length := by omega
    have hkk : k = ((k.toNat : Nat) : Int) := by omega
    rw [hkk, nth _ hk, toFrame_eq]
    exact (inChain_iff fs all m).mp hc k.toNat (by omega) hk
  · obtain ⟨⟨_, hlt⟩, hc⟩ := h m ⟨m, hm, rfl⟩
    refine ⟨by omega, (inChain_iff fs all m).mpr fun k hk hl => ?_⟩
    have := hc k ⟨by omega, by omega⟩
    rwa [nth _ hl, toFrame_eq] at this

/-- The first position of `q` whose element is not in `good`, or `0`. -/
def failingAt (q : List Int) (good : Fren.FinSet Int) : Int :=
  (((List.range q.length).find? fun i => decide (q.getD i 0 ∉ good)).map Int.ofNat).getD 0

/-- No element before `failingAt` fails. -/
theorem failingAt_first (q : List Int) (good : Fren.FinSet Int) (i : Nat) (h : (i : Int) < failingAt q good) :
    ∃ hi : i < q.length, q[i] ∈ good := by
  unfold failingAt at h
  cases e : (List.range q.length).find? (fun i => decide (q.getD i 0 ∉ good)) with
  | none => rw [e] at h; simp at h; omega
  | some k =>
    rw [e] at h
    simp only [Option.map_some, Option.getD_some, Int.ofNat_eq_natCast] at h
    obtain ⟨_, hk, hlt⟩ := List.find?_range_eq_some.mp e
    have hkl := List.mem_range.mp hk
    have hik : i < k := by omega
    refine ⟨by omega, ?_⟩
    have := hlt i hik
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < q.length)] using this

/-- Where every element is good, `failingAt` is `0`. -/
theorem failingAt_none (q : List Int) (good : Fren.FinSet Int) (h : ∀ x ∈ q, x ∈ good) :
    failingAt q good = 0 := by
  have e : (List.range q.length).find? (fun i => decide (q.getD i 0 ∉ good)) = none := by
    rw [List.find?_eq_none]
    intro i hi
    have hi := List.mem_range.mp hi
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using h _ (List.getElem_mem hi)
  unfold failingAt
  rw [e]
  rfl

-- For every sequence, set of elements, terms and value of the witness: the
-- law by which a quantifier is replaced by its instances
-- (`Fren.Core.all_iff_instances`).
impl element_witness: lang::element_witness for (q ix : List Int) (good : Fren.FinSet Int) (w : Int) {
  q := Fren.Seq.ofList q,
  good := good,
  ix := Fren.Seq.ofList ix,
  w := w,
  «all?» := q.all (· ∈ good),
  «instances?» := decide (0 ≤ w ∧ w < q.length → (Fren.Seq.ofList q).nth w ∈ good)
    && ix.all (fun t => decide (0 ≤ t ∧ t < q.length → (Fren.Seq.ofList q).nth t ∈ good)),
  failing := failingAt q good,
} by
  intro q ix good w _
  simp only [fren_spec]
  have nth (i : Nat) (h : i < q.length) : (Fren.Seq.ofList q).nth (i : Int) = q[i] := by
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using h)]; simp
  -- The quantifier, by the elements and by the positions.
  have all_iff : q.all (· ∈ good) = true ↔ ∀ t : Int, 0 ≤ t ∧ t < q.length → (Fren.Seq.ofList q).nth t ∈ good := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro h t ⟨h0, h1⟩
      have ht : t = ((t.toNat : Nat) : Int) := by omega
      rw [ht, nth _ (by omega)]
      exact h _ (List.getElem_mem _)
    · intro h x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have := h i ⟨by omega, by omega⟩
      rwa [nth _ hi] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Fren.Seq.mem_iff, List.all_eq_true]
  · simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Fren.Seq.mem_iff, Fren.Seq.toList_ofList,
      Fren.Seq.len_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun t ⟨ht, hr⟩ => h2 t ht hr⟩, fun ⟨h1, h2⟩ => ⟨h1, fun t ht hr => h2 t ⟨ht, hr⟩⟩⟩
  · intro h
    have h := all_iff.mp h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨h w, fun t _ => h t⟩
  · intro h
    have hn : ¬ ∀ t : Int, 0 ≤ t ∧ t < q.length → (Fren.Seq.ofList q).nth t ∈ good := fun h' => h (all_iff.mpr h')
    have hex : ∃ i ∈ List.range q.length, decide (q.getD i 0 ∉ good) = true := by
      apply Classical.byContradiction
      intro hne
      apply hn
      intro t ⟨h0, h1⟩
      have ht : t = ((t.toNat : Nat) : Int) := by omega
      rw [ht, nth _ (by omega)]
      apply Classical.byContradiction
      intro hg
      exact hne ⟨t.toNat, List.mem_range.mpr (by omega), by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : t.toNat < q.length), hg]⟩
    obtain ⟨i, hfind⟩ : ∃ i, (List.range q.length).find? (fun i => decide (q.getD i 0 ∉ good)) = some i := by
      cases e : (List.range q.length).find? (fun i => decide (q.getD i 0 ∉ good)) with
      | none => rw [List.find?_eq_none] at e; obtain ⟨i, hi, hp⟩ := hex; exact absurd hp (e i hi)
      | some i => exact ⟨i, rfl⟩
    have hp := List.find?_some hfind
    have hi := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
    simp only [failingAt, hfind, Option.map_some, Option.getD_some, Fren.Seq.len_eq, Fren.Seq.toList_ofList,
      Int.ofNat_eq_natCast]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [nth _ hi]
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hp
  · intro i ⟨h0, h1⟩
    have hi : i = ((i.toNat : Nat) : Int) := by omega
    obtain ⟨hl, hg⟩ := failingAt_first q good i.toNat (by rw [← hi]; exact h1)
    rw [hi, nth _ hl]
    exact hg
  · intro h
    exact failingAt_none q good (by simpa [List.all_eq_true] using h)

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
  · intro i j ⟨⟨⟨h0, hi⟩, hj0, hj⟩, hij⟩ he
    have nd := Fren.Core.nodup_indexSet s
    have hi' : i.toNat < (Fren.Core.indexSet s).length := by simp at hi; omega
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
