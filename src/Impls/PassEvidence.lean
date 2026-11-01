-- keep-sorted start
import Fren
import FrenCore.Evidence
import Impls.Check
import Reqs.Check
-- keep-sorted end
open Fren.Lang

/-! # Evidence (`Reqs/Evidence`)

`check::pass_evidence` is proved of `Fren.Core.passEvidence`, for any
number of checks and premises: the evidence that it computes for each
check, in order, from those of its premises, is its own with that of every
check that its premises reach through the premise relation's transitive
closure. `check::premise` is proved of `premised`, which `premisesOf`
enumerates, and `check::reported_pass` of `reportedPass`.

The module is named after its main component, since `Impls.Evidence` is
the module that traces every component to its evidence. -/

namespace Fren.Impls.PassEvidence

open Fren.Core (Caveat CheckEvidence passEvidence passEvidenceAux CheckKind reportedPass ReportedPass)
open Fren.Impls (toCheckedItem toCheckKind toVerdict)

def toCaveat : Caveat → check.Caveat
  | .random => .Random
  | .bounded => .Bounded

theorem toCaveat_inj {a b : Caveat} : toCaveat a = toCaveat b ↔ a = b := by
  cases a <;> cases b <;> simp [toCaveat]

/-! ## The premise relation, by positions -/

/-- The check at position `i` of `cs`, or one with no caveats, settled and
with no premises past the end. -/
def at_ (cs : List (CheckEvidence Caveat)) (i : Nat) : CheckEvidence Caveat := cs.getD i {}

/-- Check `i` takes the earlier check `j` as a premise. -/
def R (cs : List (CheckEvidence Caveat)) (i j : Nat) : Prop := i < cs.length ∧ j ∈ (at_ cs i).premises ∧ j < i

/-- Check `i` takes check `j` as a premise, earlier or not. -/
def RA (cs : List (CheckEvidence Caveat)) (i j : Nat) : Prop := i < cs.length ∧ j ∈ (at_ cs i).premises

/-- Each premise of check `i` is earlier. -/
def Earlier (cs : List (CheckEvidence Caveat)) (i : Nat) : Prop := ∀ j ∈ (at_ cs i).premises, j < i

/-- The checks that check `k` rests on, through every premise. -/
def RestsOnA (cs : List (CheckEvidence Caveat)) (k i : Nat) : Prop := i = k ∨ Relation.TransGen (RA cs) k i

/-- The checks that check `k` rests on, by the premise relation. -/
def RestsOn (cs : List (CheckEvidence Caveat)) (k i : Nat) : Prop := i = k ∨ Relation.TransGen (R cs) k i

theorem transGen_head {r : Nat → Nat → Prop} {a b c : Nat} (h : r a b) (t : Relation.TransGen r b c) :
    Relation.TransGen r a c := by
  induction t with
  | single h' => exact .tail (.single h) h'
  | tail _ h' ih => exact .tail ih h'

theorem transGen_cases {r : Nat → Nat → Prop} {a c : Nat} (t : Relation.TransGen r a c) :
    ∃ b, r a b ∧ (c = b ∨ Relation.TransGen r b c) := by
  induction t with
  | single h => exact ⟨_, h, .inl rfl⟩
  | tail _ h ih =>
    obtain ⟨b, hb, rest⟩ := ih
    rcases rest with rfl | t
    · exact ⟨_, hb, .inr (.single h)⟩
    · exact ⟨_, hb, .inr (.tail t h)⟩

/-- What check `k` rests on, one premise at a time. -/
theorem restsOn_iff (cs : List (CheckEvidence Caveat)) (k i : Nat) :
    RestsOn cs k i ↔ i = k ∨ ∃ j, R cs k j ∧ RestsOn cs j i := by
  unfold RestsOn
  constructor
  · rintro (rfl | t)
    · exact .inl rfl
    · obtain ⟨b, hb, rest⟩ := transGen_cases t
      exact .inr ⟨b, hb, rest⟩
  · rintro (rfl | ⟨j, hj, rfl | t⟩)
    · exact .inl rfl
    · exact .inr (.single hj)
    · exact .inr (transGen_head hj t)

/-! ## The evidence that `passEvidence` computes -/

/-- The evidence of check `k`, as the spec has it: the caveats of the checks
that it rests on, and whether all of them are settled. -/
def Correct (cs : List (CheckEvidence Caveat)) (k : Nat) (e : List Caveat × Bool) : Prop :=
  (∀ c, c ∈ e.1 ↔ ∃ i, RestsOn cs k i ∧ c ∈ (at_ cs i).own) ∧
    (e.2 = true ↔ ∀ i, RestsOn cs k i → (at_ cs i).settled = true ∧ Earlier cs i)

theorem aux_correct (cs : List (CheckEvidence Caveat)) :
    ∀ (rest : List (CheckEvidence Caveat)) (acc : Array (List Caveat × Bool)),
      rest = cs.drop acc.size → acc.size ≤ cs.length →
      (∀ k (h : k < acc.size), Correct cs k acc[k]) →
      (passEvidenceAux rest acc).size = cs.length ∧
        ∀ k (h : k < (passEvidenceAux rest acc).size), Correct cs k (passEvidenceAux rest acc)[k] := by
  intro rest
  induction rest with
  | nil =>
    intro acc hrest hle hacc
    have : acc.size = cs.length := by
      have := congrArg List.length hrest
      simp at this
      omega
    exact ⟨this, hacc⟩
  | cons c rest ih =>
    intro acc hrest hle hacc
    have hlt : acc.size < cs.length := by
      have := congrArg List.length hrest
      simp at this
      omega
    have hc : at_ cs acc.size = c := by
      have h1 : cs[acc.size]? = some c := by
        have := congrArg List.head? hrest
        rw [List.head?_drop] at this
        exact this.symm
      simp [at_, List.getD_eq_getElem?_getD, h1]
    have hrest' : rest = cs.drop (acc.size + 1) := by
      have := congrArg List.tail hrest
      simpa [List.tail_drop] using this
    apply ih
    · simpa using hrest'
    · simp; omega
    · intro k hk
      simp only [Array.size_push] at hk
      by_cases hka : k < acc.size
      · rw [Array.getElem_push_lt hka]
        exact hacc k hka
      · have hk' : k = acc.size := by omega
        subst hk'
        rw [Array.getElem_push_eq]
        -- The new check: its own, with its premises', which are earlier.
        have hR : ∀ j, R cs acc.size j ↔ j ∈ c.premises ∧ j < acc.size := by
          intro j
          simp only [R, hc]
          exact ⟨fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨hlt, h1, h2⟩⟩
        constructor
        · intro x
          simp only [List.mem_eraseDups, List.mem_append, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          rw [show (∃ i, RestsOn cs acc.size i ∧ x ∈ (at_ cs i).own) ↔
              (x ∈ c.own ∨ ∃ j, R cs acc.size j ∧ ∃ i, RestsOn cs j i ∧ x ∈ (at_ cs i).own) by
            constructor
            · rintro ⟨i, hi, hx⟩
              rcases (restsOn_iff cs _ i).mp hi with rfl | ⟨j, hj, hji⟩
              · exact .inl (hc ▸ hx)
              · exact .inr ⟨j, hj, i, hji, hx⟩
            · rintro (hx | ⟨j, hj, i, hji, hx⟩)
              · exact ⟨_, .inl rfl, hc ▸ hx⟩
              · exact ⟨i, (restsOn_iff cs _ i).mpr (.inr ⟨j, hj, hji⟩), hx⟩]
          apply or_congr Iff.rfl
          constructor
          · rintro ⟨j, ⟨hjp, hjl⟩, hx⟩
            have := (hacc j hjl).1 x
            rw [Array.getElem?_eq_getElem hjl] at hx
            simp only [Option.map_some, Option.getD_some] at hx
            exact ⟨j, (hR j).mpr ⟨hjp, hjl⟩, this.mp hx⟩
          · rintro ⟨j, hj, hx⟩
            obtain ⟨hjp, hjl⟩ := (hR j).mp hj
            refine ⟨j, ⟨hjp, hjl⟩, ?_⟩
            rw [Array.getElem?_eq_getElem hjl]
            simp only [Option.map_some, Option.getD_some]
            exact ((hacc j hjl).1 x).mpr hx
        · simp only [Bool.and_eq_true, List.all_eq_true, List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro ⟨⟨hs, hearly⟩, hps⟩ i hi
            rcases (restsOn_iff cs _ i).mp hi with rfl | ⟨j, hj, hji⟩
            · exact ⟨by rw [hc]; exact hs, by unfold Earlier; rw [hc]; exact hearly⟩
            · obtain ⟨hjp, hjl⟩ := (hR j).mp hj
              have := hps j ⟨hjp, hjl⟩
              rw [Array.getElem?_eq_getElem hjl] at this
              simp only [Option.map_some, Option.getD_some] at this
              exact ((hacc j hjl).2.mp this) i hji
          · intro h
            have h0 := h _ (.inl rfl)
            have h0s := h0.1
            have h0e := h0.2
            unfold Earlier at h0e
            rw [hc] at h0s h0e
            refine ⟨⟨h0s, h0e⟩, fun j ⟨hjp, hjl⟩ => ?_⟩
            rw [Array.getElem?_eq_getElem hjl]
            simp only [Option.map_some, Option.getD_some]
            exact (hacc j hjl).2.mpr fun i hji => h i ((restsOn_iff cs _ i).mpr (.inr ⟨j, (hR j).mpr ⟨hjp, hjl⟩, hji⟩))

theorem passEvidence_correct (cs : List (CheckEvidence Caveat)) :
    (passEvidence cs).size = cs.length ∧ ∀ k (h : k < (passEvidence cs).size), Correct cs k (passEvidence cs)[k] :=
  aux_correct cs cs #[] (by simp) (by simp) (by simp)

/-! ## Every premise against the earlier ones -/

theorem restsOnA_of_restsOn (cs : List (CheckEvidence Caveat)) (k i : Nat) (h : RestsOn cs k i) : RestsOnA cs k i := by
  rcases h with rfl | t
  · exact .inl rfl
  · refine .inr ?_
    induction t with
    | single h => exact .single ⟨h.1, h.2.1⟩
    | tail _ h ih => exact .tail ih ⟨h.1, h.2.1⟩

/-- Where every check that `k` rests on through its earlier premises has
only earlier premises, it rests on no other check through every premise. -/
theorem restsOn_of_restsOnA (cs : List (CheckEvidence Caveat)) (k : Nat)
    (he : ∀ i, RestsOn cs k i → Earlier cs i) (i : Nat) (h : RestsOnA cs k i) : RestsOn cs k i := by
  rcases h with rfl | t
  · exact .inl rfl
  · induction t with
    | single h =>
      exact .inr (.single ⟨h.1, h.2, he k (.inl rfl) _ h.2⟩)
    | tail _ h ih =>
      have hb := ih
      have hlt := he _ hb _ h.2
      rcases hb with rfl | tb
      · exact .inr (.single ⟨h.1, h.2, hlt⟩)
      · exact .inr (.tail tb ⟨h.1, h.2, hlt⟩)

/-! ## The spec's sets and relations -/

/-- The caveats of each check's own method, by position. -/
def ownPairs (cs : List (CheckEvidence Caveat)) : List (Int × check.Caveat) :=
  (List.range cs.length).flatMap fun i => (at_ cs i).own.map fun c => ((i : Int), toCaveat c)

/-- The checks whose own verdict is not a pass. -/
def unsettledOf (cs : List (CheckEvidence Caveat)) : List Int :=
  ((List.range cs.length).filter fun i => !(at_ cs i).settled).map fun (i : Nat) => (i : Int)

/-- The premise relation, by positions. -/
def premisePairs (cs : List (CheckEvidence Caveat)) : List (Int × Int) :=
  (List.range cs.length).flatMap fun (i : Nat) => (at_ cs i).premises.map fun (j : Nat) => ((i : Int), (j : Int))

theorem mem_premisePairs_raw (cs : List (CheckEvidence Caveat)) (a b : Int) :
    (a, b) ∈ premisePairs cs ↔ ∃ i j : Nat, a = i ∧ b = j ∧ i < cs.length ∧ j ∈ (at_ cs i).premises := by
  simp only [premisePairs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, j, hj, rfl, rfl⟩
    exact ⟨i, j, rfl, rfl, hi, hj⟩
  · rintro ⟨i, j, rfl, rfl, hi, hj⟩
    exact ⟨i, hi, j, hj, rfl, rfl⟩

theorem mem_premisePairs (cs : List (CheckEvidence Caveat)) (a b : Int) :
    (a, b) ∈ premisePairs cs ↔ ∃ i j : Nat, a = i ∧ b = j ∧ RA cs i j := by
  rw [mem_premisePairs_raw]
  rfl

/-- The premise relation over `Int`s is the one over positions. -/
theorem transGen_int (cs : List (CheckEvidence Caveat)) (k : Nat) (y : Int) :
    Relation.TransGen (fun x y => (x, y) ∈ Fren.FinSet.ofList (premisePairs cs)) (k : Int) y ↔
      ∃ i : Nat, y = i ∧ Relation.TransGen (RA cs) k i := by
  constructor
  · intro t
    generalize hx : (k : Int) = x at t
    induction t with
    | single h =>
      rw [Fren.FinSet.mem_ofList, mem_premisePairs] at h
      obtain ⟨i, j, rfl, rfl, hr⟩ := h
      have : i = k := by omega
      subst this
      exact ⟨j, rfl, .single hr⟩
    | tail _ h ih =>
      obtain ⟨b, rfl, tb⟩ := ih
      rw [Fren.FinSet.mem_ofList, mem_premisePairs] at h
      obtain ⟨i, j, hi, rfl, hr⟩ := h
      have : i = b := by omega
      subst this
      exact ⟨j, rfl, .tail tb hr⟩
  · rintro ⟨i, rfl, t⟩
    induction t with
    | single h =>
      exact .single (by rw [Fren.FinSet.mem_ofList, mem_premisePairs]; exact ⟨_, _, rfl, rfl, h⟩)
    | tail _ h ih =>
      exact .tail ih (by rw [Fren.FinSet.mem_ofList, mem_premisePairs]; exact ⟨_, _, rfl, rfl, h⟩)

theorem mem_restsOn (cs : List (CheckEvidence Caveat)) (k : Nat) (y : Int) :
    y ∈ check.rests_on (Fren.FinSet.ofList (premisePairs cs)) k ↔ ∃ i : Nat, y = i ∧ RestsOnA cs k i := by
  simp only [check.rests_on, fren_spec, Fren.FinSet.mem_union, Fren.FinSet.mem_singleton, Fren.FinSet.mem_image,
    Fren.FinSet.mem_closure]
  constructor
  · rintro (rfl | ⟨a, rfl, t⟩)
    · exact ⟨k, rfl, .inl rfl⟩
    · obtain ⟨i, hy, t'⟩ := (transGen_int cs k y).mp t
      exact ⟨i, hy, .inr t'⟩
  · rintro ⟨i, rfl, rfl | t⟩
    · exact .inl rfl
    · exact .inr ⟨k, rfl, (transGen_int cs k i).mpr ⟨i, rfl, t⟩⟩

theorem mem_ownPairs (cs : List (CheckEvidence Caveat)) (i : Nat) (c : check.Caveat) :
    ((i : Int), c) ∈ ownPairs cs ↔ i < cs.length ∧ ∃ c', c' ∈ (at_ cs i).own ∧ toCaveat c' = c := by
  simp only [ownPairs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, c', hc', hij, rfl⟩
    have : j = i := by omega
    subst this
    exact ⟨hj, c', hc', rfl⟩
  · rintro ⟨hi, c', hc', rfl⟩
    exact ⟨i, hi, c', hc', rfl, rfl⟩

theorem at_past (cs : List (CheckEvidence Caveat)) (i : Nat) (h : ¬ i < cs.length) : at_ cs i = {} := by
  simp only [at_, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show cs.length ≤ i by omega), Option.getD_none]

-- Both front ends compute the evidence of every check with `passEvidence`
-- (`itemEvidence`), from each check's own caveats and verdict and its
-- premises, which `premisesOf` gives.
impl pass_evidence: check::pass_evidence for (cs : List (CheckEvidence Caveat)) (k : Nat) {
  own := Fren.FinSet.ofList (ownPairs cs),
  unsettled := Fren.FinSet.ofList (unsettledOf cs),
  premises := Fren.FinSet.ofList (premisePairs cs),
  k := (k : Int),
  «random?» := (((passEvidence cs)[k]?.map (·.1)).getD []).contains .random,
  «bounded?» := (((passEvidence cs)[k]?.map (·.1)).getD []).contains .bounded,
  «settled?» := ((passEvidence cs)[k]?.map (·.2)).getD true,
} by
  intro cs k _
  unfold check.pass_evidence.ensures check.pass_evidence.ensure.random_rule check.pass_evidence.ensure.bounded_rule
    check.pass_evidence.ensure.settled_rule
  obtain ⟨_, hcorrect⟩ := passEvidence_correct cs
  -- The evidence of `k` as `Correct` has it, also past the last check.
  have hk : Correct cs k (((passEvidence cs)[k]?.map (·.1)).getD [], ((passEvidence cs)[k]?.map (·.2)).getD true) := by
    by_cases h : k < (passEvidence cs).size
    · rw [Array.getElem?_eq_getElem h]
      exact hcorrect k h
    · rw [Array.getElem?_eq_none (by omega)]
      have hnone : ∀ i, RestsOn cs k i → i = k := by
        rintro i (rfl | t)
        · rfl
        · obtain ⟨b, ⟨hb, _⟩, _⟩ := transGen_cases t
          omega
      refine ⟨fun c => ⟨fun h => by simp at h, fun ⟨i, hi, hc⟩ => ?_⟩, ⟨fun _ i hi => ?_, fun _ => rfl⟩⟩
      · rw [hnone i hi, at_past cs k (by omega)] at hc
        simp at hc
      · rw [hnone i hi]
        refine ⟨by rw [at_past cs k (by omega)], fun j hj => ?_⟩
        rw [at_past cs k (by omega)] at hj
        simp at hj
  have hpast (i : Nat) (h : ¬ i < cs.length) : Earlier cs i := by
    intro j hj
    rw [at_past cs i h] at hj
    simp at hj
  -- The spec's `earlier?`: every premise of every check that `k` rests on is
  -- earlier.
  have hE : check.earlier? (Fren.FinSet.ofList (premisePairs cs)) (k : Int) ↔ ∀ i, RestsOnA cs k i → Earlier cs i := by
    unfold check.earlier?
    simp only [fren_spec, decide_eq_true_eq]
    constructor
    · intro h i hi j hj
      rcases Nat.lt_or_ge i cs.length with hil | hil
      · have := h (i : Int) (j : Int) ⟨(mem_restsOn cs k i).mpr ⟨i, rfl, hi⟩,
          by rw [Fren.FinSet.mem_ofList, mem_premisePairs]; exact ⟨i, j, rfl, rfl, hil, hj⟩⟩
        omega
      · exact hpast i (by omega) j hj
    · rintro h a b ⟨ha, hab⟩
      obtain ⟨i, rfl, hi⟩ := (mem_restsOn cs k a).mp ha
      rw [Fren.FinSet.mem_ofList, mem_premisePairs] at hab
      obtain ⟨i', j, hi', rfl, hr⟩ := hab
      have : i' = i := by omega
      subst this
      have := h i' hi j hr.2
      omega
  have hRA (he : ∀ i, RestsOn cs k i → Earlier cs i) (i : Nat) : RestsOnA cs k i ↔ RestsOn cs k i :=
    ⟨restsOn_of_restsOnA cs k he i, restsOnA_of_restsOn cs k i⟩
  have hmem (he : ∀ i, RestsOn cs k i → Earlier cs i) : ∀ cv : Caveat,
      (((passEvidence cs)[k]?.map (·.1)).getD []).contains cv = true ↔
      toCaveat cv ∈ Fren.FinSet.image (Fren.FinSet.ofList (ownPairs cs)) (check.rests_on (Fren.FinSet.ofList (premisePairs cs)) k) := by
    intro cv
    rw [List.contains_iff_mem, Fren.FinSet.mem_image]
    simp only [mem_restsOn cs k, hRA he]
    constructor
    · intro hc'
      obtain ⟨i, hi, hc''⟩ := (hk.1 cv).mp hc'
      have hil : i < cs.length := by
        rcases Nat.lt_or_ge i cs.length with hn | hn
        · exact hn
        · rw [at_past cs i (by omega)] at hc''
          simp at hc''
      exact ⟨i, ⟨i, rfl, hi⟩, (mem_ownPairs cs i _).mpr ⟨hil, cv, hc'', rfl⟩⟩
    · rintro ⟨y, ⟨i, rfl, hi⟩, hy⟩
      obtain ⟨_, c', hc', he'⟩ := (mem_ownPairs cs i _).mp hy
      rw [toCaveat_inj] at he'
      subst he'
      exact (hk.1 c').mpr ⟨i, hi, hc'⟩
  have hempty (y : Int) : y ∉ (∅ : Fren.FinSet Int) := by
    simp [EmptyCollection.emptyCollection]
  have hunsettled (i : Nat) : ((i : Int) ∈ Fren.FinSet.ofList (unsettledOf cs)) ↔ (at_ cs i).settled = false := by
    simp only [Fren.FinSet.mem_ofList, unsettledOf, List.mem_map, List.mem_filter, List.mem_range, Bool.not_eq_true']
    constructor
    · rintro ⟨j, ⟨_, hs⟩, hji⟩
      have : j = i := by omega
      exact this ▸ hs
    · intro hs
      have hil : i < cs.length := by
        rcases Nat.lt_or_ge i cs.length with hn | hn
        · exact hn
        · rw [at_past cs i (by omega)] at hs
          simp at hs
      exact ⟨i, ⟨hil, hs⟩, rfl⟩
  refine ⟨fun hEar => hmem (fun i hi => (hE.mp hEar) i (restsOnA_of_restsOn cs k i hi)) .random,
    fun hEar => hmem (fun i hi => (hE.mp hEar) i (restsOnA_of_restsOn cs k i hi)) .bounded, ?_⟩
  constructor
  · intro hs
    have hall := hk.2.mp hs
    have he : ∀ i, RestsOn cs k i → Earlier cs i := fun i hi => (hall i hi).2
    refine ⟨?_, hE.mpr fun i hi => he i ((hRA he i).mp hi)⟩
    apply Fren.FinSet.ext
    intro y
    rw [Fren.FinSet.mem_inter, mem_restsOn]
    constructor
    · rintro ⟨⟨i, rfl, hi⟩, hy⟩
      exfalso
      rw [hunsettled] at hy
      have := (hall i ((hRA he i).mp hi)).1
      rw [hy] at this
      cases this
    · intro hy
      exact absurd hy (hempty y)
  · rintro ⟨hemp, hEar⟩
    apply hk.2.mpr
    intro i hi
    refine ⟨?_, (hE.mp hEar) i (restsOnA_of_restsOn cs k i hi)⟩
    cases hsi : (at_ cs i).settled
    · exfalso
      have hin : (i : Int) ∈ check.rests_on (Fren.FinSet.ofList (premisePairs cs)) k ∩
          Fren.FinSet.ofList (unsettledOf cs) := by
        rw [Fren.FinSet.mem_inter, mem_restsOn, hunsettled]
        exact ⟨⟨i, rfl, restsOnA_of_restsOn cs k i hi⟩, hsi⟩
      rw [hemp] at hin
      exact hempty _ hin
    · rfl

/-! ## Premises and reports -/

def toSite : Fren.Core.Site → check.Site
  | .whole => .Whole
  | .assumption => .Assumption
  | .constraint => .Constraint
  | .callArgument k => .CallArgument k
  | .callAssumption k => .CallAssumption k
  | .functionClause f => .FunctionClause f
  | .constant => .Constant
  | .refinement a => .Refinement a

def toPremise : Fren.Core.Premise → check.Premise
  | .realizability j => .Realizability j
  | .callAssumptions j => .CallAssumptions j
  | .ownRealizability => .OwnRealizability
  | .abstractionRealizability a => .AbstractionRealizability a
  | .contractRealizability f => .ContractRealizability f
  | .instanceContract i => .InstanceContract i
  | .postconditions f => .Postconditions f
  | .inhabitation t => .Inhabitation t

def toFnKind : Fren.Core.FnKind → check.FnKind
  | .contract => .Contract
  | .instance => .Instance
  | .recursive => .Recursive
  | .defined => .Defined

def toRecord (c : Fren.Core.CheckRecord) : check.CheckRecord :=
  ⟨toCheckedItem c.item, toCheckKind c.kind, toSite c.site,
    Fren.FinSet.ofList (c.applies.map fun (f : Nat) => (f : Int)),
    Fren.FinSet.ofList (c.types.map fun (t : Nat) => (t : Int))⟩

def toKinds (kinds : List (Nat × Fren.Core.FnKind)) : Fren.FinSet (Int × check.FnKind) :=
  Fren.FinSet.ofList (kinds.map fun (f, k) => ((f : Int), toFnKind k))

theorem mem_nats (l : List Nat) (f : Nat) : ((f : Int) ∈ Fren.FinSet.ofList (l.map fun (f : Nat) => (f : Int))) ↔ l.contains f = true := by
  simp only [Fren.FinSet.mem_ofList, List.mem_map, List.contains_iff_mem]
  constructor
  · rintro ⟨g, hg, he⟩
    have : g = f := by omega
    exact this ▸ hg
  · intro h
    exact ⟨f, h, rfl⟩

theorem mem_kinds (kinds : List (Nat × Fren.Core.FnKind)) (f : Nat) (k : Fren.Core.FnKind) :
    (((f : Int), toFnKind k) ∈ toKinds kinds) ↔ kinds.contains (f, k) = true := by
  simp only [toKinds, Fren.FinSet.mem_ofList, List.mem_map, List.contains_iff_mem, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨g, k'⟩, hg, he, hk⟩
    have : g = f := by omega
    have hk' : k' = k := by cases k <;> cases k' <;> simp_all [toFnKind]
    subst this; subst hk'
    exact hg
  · intro h
    exact ⟨(f, k), h, rfl, rfl⟩

-- Both front ends take as a check's premises those of `premisesOf`
-- (`itemEvidence`), which are those that `premised` takes.
impl premise: check::premise for (c : Fren.Core.CheckRecord) (n : Nat) (kinds : List (Nat × Fren.Core.FnKind))
    (p : Fren.Core.Premise) {
  check := toRecord c,
  n_calls := n,
  kinds := toKinds kinds,
  p := toPremise p,
  «premised?» := Fren.Core.premised c n kinds p,
} by
  intro c n kinds p
  unfold check.premise.ensures check.premise.ensure.rule
  intro _
  rcases c with ⟨item, k, site, applies, types⟩
  have hk : Fren.Core.CheckKind.proof k = true ↔ check.proof? (toCheckKind k) = true := by
    cases k <;> simp [fren_spec, toCheckKind, Fren.Core.CheckKind.proof, check.proof?]
  simp only [Fren.Core.premised, toRecord, toPremise, Bool.and_eq_true, hk]
  apply and_congr_right
  intro _
  cases p with
  | realizability j | callAssumptions j =>
    cases site <;> simp [fren_spec, toSite, Fren.Core.Site.hasCall, check.has_call?, check.Premise.Realizability.x0,
      check.Premise.CallAssumptions.x0, check.Site.CallArgument.x0, check.Site.CallAssumption.x0] <;> omega
  | ownRealizability =>
    have hk2 : (k != Fren.Core.CheckKind.realizable) = true ↔ ¬ toCheckKind k = check.Kind.Realizability := by
      cases k <;> simp [toCheckKind]
    -- An item has a realizability check of its own exactly where
    -- `check::applies` runs one (`check::own_realizability?`).
    have hi : item.ownRealizability = true ↔ check.own_realizability? (toCheckedItem item) = true := by
      cases item <;> simp [fren_spec, toCheckedItem, Fren.Core.CheckedItem.ownRealizability,
        Fren.Core.CheckedItem.kinds, Fren.Core.kindsFor, Fren.Core.CheckKind.all, Fren.Core.globalKinds,
        Fren.Core.bodyKinds, Fren.Core.contractKinds, check.own_realizability?]
    cases site <;> simp [fren_spec, toSite, Fren.Core.Site.ownHypotheses, check.own_hypotheses?, hk2, hi]
  | abstractionRealizability a =>
    cases site <;> simp [fren_spec, toSite, check.Premise.AbstractionRealizability.x0] <;>
      omega
  | contractRealizability f | instanceContract f | postconditions f =>
    have ha := mem_nats applies f
    have hc := mem_kinds kinds f .contract
    have hi := mem_kinds kinds f .instance
    have hr := mem_kinds kinds f .recursive
    simp only [toFnKind] at hc hi hr
    cases site <;> simp [fren_spec, toSite, Fren.Core.Site.ownFunction, check.own_function?, ha, hc, hi, hr,
      check.Premise.ContractRealizability.x0, check.Premise.InstanceContract.x0, check.Premise.Postconditions.x0,
      check.Site.FunctionClause.x0] <;> omega
  | inhabitation t =>
    have ht := mem_nats types t
    simp [fren_spec, ht, check.Premise.Inhabitation.x0]

/-- `premisesOf` lists exactly the premises that `premised` takes. -/
theorem mem_premisesOf (c : Fren.Core.CheckRecord) (n : Nat) (kinds : List (Nat × Fren.Core.FnKind)) (p : Fren.Core.Premise) :
    p ∈ Fren.Core.premisesOf c n kinds ↔ Fren.Core.premised c n kinds p = true := by
  unfold Fren.Core.premisesOf
  rw [List.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rcases c with ⟨item, k, site, applies, types⟩
  cases p with
  | realizability j =>
    have : j < n := by
      simp only [Fren.Core.premised, Fren.Core.Site.hasCall, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2.1
    have hm : Fren.Core.Premise.realizability j ∈ (List.range n).flatMap
        (fun j => [Fren.Core.Premise.realizability j, Fren.Core.Premise.callAssumptions j]) :=
      List.mem_flatMap.mpr ⟨j, List.mem_range.mpr this, by simp⟩
    simp [List.mem_append, hm]
  | callAssumptions j =>
    have : j < n := by
      simp only [Fren.Core.premised, Fren.Core.Site.hasCall, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2.1
    have hm : Fren.Core.Premise.callAssumptions j ∈ (List.range n).flatMap
        (fun j => [Fren.Core.Premise.realizability j, Fren.Core.Premise.callAssumptions j]) :=
      List.mem_flatMap.mpr ⟨j, List.mem_range.mpr this, by simp⟩
    simp [List.mem_append, hm]
  | ownRealizability => simp
  | abstractionRealizability a =>
    simp only [Fren.Core.premised, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.2]
  | contractRealizability f =>
    simp only [Fren.Core.premised, Bool.and_eq_true, List.contains_iff_mem] at h
    have hm : Fren.Core.Premise.contractRealizability f ∈ applies.flatMap (fun f => [Fren.Core.Premise.contractRealizability f,
        Fren.Core.Premise.instanceContract f, Fren.Core.Premise.postconditions f]) :=
      List.mem_flatMap.mpr ⟨f, h.2.1.1, by simp⟩
    simp [List.mem_append, hm]
  | instanceContract f =>
    simp only [Fren.Core.premised, Bool.and_eq_true, List.contains_iff_mem] at h
    have hm : Fren.Core.Premise.instanceContract f ∈ applies.flatMap (fun f => [Fren.Core.Premise.contractRealizability f,
        Fren.Core.Premise.instanceContract f, Fren.Core.Premise.postconditions f]) :=
      List.mem_flatMap.mpr ⟨f, h.2.1.1, by simp⟩
    simp [List.mem_append, hm]
  | postconditions f =>
    simp only [Fren.Core.premised, Bool.and_eq_true, List.contains_iff_mem] at h
    have hm : Fren.Core.Premise.postconditions f ∈ applies.flatMap (fun f => [Fren.Core.Premise.contractRealizability f,
        Fren.Core.Premise.instanceContract f, Fren.Core.Premise.postconditions f]) :=
      List.mem_flatMap.mpr ⟨f, h.2.1.1, by simp⟩
    simp [List.mem_append, hm]
  | inhabitation t =>
    simp only [Fren.Core.premised, Bool.and_eq_true, List.contains_iff_mem] at h
    have hm : Fren.Core.Premise.inhabitation t ∈ types.map Fren.Core.Premise.inhabitation := List.mem_map.mpr ⟨t, h.2, rfl⟩
    simp [List.mem_append, hm]

-- Both front ends take an item's premises from its structure with
-- `itemHasPremise` (`itemEvidence`), and a premise that it has with no
-- result is a check that is not settled.
impl item_premise: check::item_premise for (item : Fren.Core.CheckedItem) (v : Bool) (n : Nat) (assumed : List Nat)
    (na nf : Nat) (p : Fren.Core.Premise) {
  item := toCheckedItem item,
  «validator?» := v,
  n_calls := n,
  assumed := Fren.FinSet.ofList (assumed.map fun (j : Nat) => (j : Int)),
  n_abstractions := na,
  n_functions := nf,
  p := toPremise p,
  «has?» := Fren.Core.itemHasPremise item v n assumed na nf p,
} by
  intro item v n assumed na nf p
  unfold check.item_premise.ensures check.item_premise.ensure.rule
  intro _
  have hi : item.ownRealizability = true ↔ check.own_realizability? (toCheckedItem item) = true := by
    cases item <;> simp [fren_spec, toCheckedItem, Fren.Core.CheckedItem.ownRealizability,
      Fren.Core.CheckedItem.kinds, Fren.Core.kindsFor, Fren.Core.CheckKind.all, Fren.Core.globalKinds,
      Fren.Core.bodyKinds, Fren.Core.contractKinds, check.own_realizability?]
  cases p with
  | realizability j =>
    simp [fren_spec, Fren.Core.itemHasPremise, toPremise, check.Premise.Realizability.x0]
  | callAssumptions j =>
    have ha := mem_nats assumed j
    cases item <;> simp [fren_spec, Fren.Core.itemHasPremise, toPremise, toCheckedItem, ha,
      check.Premise.CallAssumptions.x0] <;> omega
  | ownRealizability =>
    simp [fren_spec, Fren.Core.itemHasPremise, toPremise, hi]
  | abstractionRealizability a =>
    simp [fren_spec, Fren.Core.itemHasPremise, toPremise, check.Premise.AbstractionRealizability.x0]
  | contractRealizability f =>
    simp [fren_spec, Fren.Core.itemHasPremise, toPremise, check.Premise.ContractRealizability.x0]
  | _ => simp [fren_spec, Fren.Core.itemHasPremise, toPremise]

def toFact : Fren.Core.AppFact Nat → check.Fact
  | .nat => .AtLeastZero
  | .type => .ResultType
  | .postcondition f => .Postcondition f

theorem mem_queriedFns (facts : List (Fren.Core.AppFact Nat)) (f : Nat) :
    f ∈ Fren.Core.queriedFns facts ↔ Fren.Core.AppFact.postcondition f ∈ facts := by
  unfold Fren.Core.queriedFns
  rw [List.mem_eraseDups, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩
    cases a <;> simp at h
    subst h; exact ha
  · intro h; exact ⟨_, h, rfl⟩

-- Both front ends' query builders take the functions whose contracts a
-- query's facts bring with `queriedFns`, over what each fact is
-- (`appFactsWith`, `appFactKinds`).
impl query_applies: check::query_applies for (facts : List (Fren.Core.AppFact Nat)) (f : Nat) {
  facts := Fren.FinSet.ofList (facts.map toFact),
  f := (f : Int),
  «applied?» := (Fren.Core.queriedFns facts).contains f,
} by
  intro facts f _
  unfold check.query_applies.ensures check.query_applies.ensure.rule
  rw [List.contains_iff_mem, mem_queriedFns, Fren.FinSet.mem_ofList, List.mem_map]
  constructor
  · intro h; exact ⟨_, h, rfl⟩
  · rintro ⟨a, ha, he⟩
    cases a <;> simp [toFact] at he
    have : _ := Int.ofNat_inj.mp he
    subst this; exact ha

-- Both front ends' query builders keep the applications that bring facts
-- with `appBrings`, given the item's function (`Comp.fn?`), if it is one,
-- for every query of the item (`appFactsWith`).
impl query_facts: check::query_facts for (own? : Option Nat) (f : Nat) {
  «own_fn?» := own?.isSome,
  g := ((own?.getD 0 : Nat) : Int),
  f := (f : Int),
  «brings?» := Fren.Core.appBrings own? (some f),
} by
  intro own? f _
  unfold check.query_facts.ensures check.query_facts.ensure.rule
  cases own? <;> simp [fren_spec, Fren.Core.appBrings] <;> omega

/-! ## The applications whose facts a query has (`check::fact_applications`) -/

theorem mem_newApps {F : Type} [BEq F] [LawfulBEq F] (brings : F → Bool) (seen found : List F) (b : F) :
    b ∈ Fren.Core.newApps brings seen found ↔ b ∈ found ∧ brings b = true ∧ b ∉ seen := by
  simp [Fren.Core.newApps, List.mem_eraseDups, List.mem_filter]

/-- What `closeApps` ends with, from `seen`, `work` and `acc` that meet its
invariant: every application `seen` is one of `acc`'s or `work`'s, and the
applications in the facts of `acc`'s that bring theirs are `seen`. Then
those in the facts of its applications that bring theirs are its own, it
has every one `seen`, and, where `acc`'s and `work`'s bring theirs, so
does each of its. -/
theorem closeApps_spec {F α : Type} [BEq F] [LawfulBEq F] (brings : F → Bool) (inside : F → Id (α × List F)) :
    ∀ (n : Nat) (seen work : List F) (acc r : List (F × α)),
    (∀ x, x ∈ seen ↔ x ∈ acc.map (·.1) ∨ x ∈ work) →
    (∀ p ∈ acc, ∀ b ∈ (inside p.1).run.2, brings b = true → b ∈ seen) →
    (Fren.Core.closeApps brings inside n seen work acc).run = some r →
    (∀ p ∈ r, ∀ b ∈ (inside p.1).run.2, brings b = true → b ∈ r.map (·.1)) ∧
    (∀ x ∈ seen, x ∈ r.map (·.1)) ∧
    ((∀ x, x ∈ acc.map (·.1) ∨ x ∈ work → brings x = true) → ∀ x ∈ r.map (·.1), brings x = true) := by
  intro n
  induction n with
  | zero =>
    intro seen work acc r h1 h2 hr
    cases work with
    | nil =>
      simp [Fren.Core.closeApps] at hr
      subst hr
      refine ⟨fun p hp b hb hbr => ?_, fun x hx => ?_, fun h x hx => h x (.inl hx)⟩
      · have := (h1 b).mp (h2 p hp b hb hbr); simpa using this
      · have := (h1 x).mp hx; simpa using this
    | cons w ws => simp [Fren.Core.closeApps] at hr
  | succ n ih =>
    intro seen work acc r h1 h2 hr
    cases work with
    | nil =>
      simp [Fren.Core.closeApps] at hr
      subst hr
      refine ⟨fun p hp b hb hbr => ?_, fun x hx => ?_, fun h x hx => h x (.inl hx)⟩
      · have := (h1 b).mp (h2 p hp b hb hbr); simpa using this
      · have := (h1 x).mp hx; simpa using this
    | cons w ws =>
      simp only [Fren.Core.closeApps, Id.run_bind, List.idRun_mapM] at hr
      generalize hrs : (w :: ws).map (fun a => (inside a).run) = rs at hr
      have hlen : (w :: ws).length ≤ (rs.map (·.1)).length := by subst hrs; simp
      have hfst : ((w :: ws).zip (rs.map (·.1))).map (·.1) = w :: ws := List.map_fst_zip hlen
      have hin : ∀ a ∈ w :: ws, ∀ b ∈ (inside a).run.2, b ∈ rs.flatMap (·.2) := by
        intro a ha b hb
        subst hrs
        simp only [List.mem_flatMap, List.mem_map]
        exact ⟨_, ⟨a, ha, rfl⟩, hb⟩
      have i1 : ∀ x, x ∈ seen ++ Fren.Core.newApps brings seen (rs.flatMap (·.2)) ↔
          x ∈ (acc ++ (w :: ws).zip (rs.map (·.1))).map (·.1) ∨ x ∈ Fren.Core.newApps brings seen (rs.flatMap (·.2)) := by
        intro x
        rw [List.map_append, hfst, List.mem_append, List.mem_append, h1 x]
      have i2 : ∀ p ∈ acc ++ (w :: ws).zip (rs.map (·.1)), ∀ b ∈ (inside p.1).run.2, brings b = true →
          b ∈ seen ++ Fren.Core.newApps brings seen (rs.flatMap (·.2)) := by
        intro p hp b hb hbr
        rw [List.mem_append] at hp ⊢
        rcases hp with hp | hp
        · exact .inl (h2 p hp b hb hbr)
        · have hw := (List.of_mem_zip hp).1
          by_cases hs : b ∈ seen
          · exact .inl hs
          · exact .inr ((mem_newApps _ _ _ _).mpr ⟨hin _ hw b hb, hbr, hs⟩)
      obtain ⟨c1, c2, c3⟩ := ih _ _ _ r i1 i2 hr
      refine ⟨c1, fun x hx => c2 x (List.mem_append_left _ hx), fun h => c3 fun x hx => ?_⟩
      rw [List.map_append, hfst, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact h x (.inl hx)
      · exact h x (.inr hx)
      · exact ((mem_newApps _ _ _ _).mp hx).2.1

/-- The applications that the facts of `a` mention, of the pairs `rel`. -/
def insideOf (rel : List (Nat × Nat)) (a : Nat) : Id (Unit × List Nat) :=
  pure ((), (rel.filter (·.1 == a)).map (·.2))

-- Both front ends' query builders take the applications whose facts a
-- query has from `closeApps`, from those that its formulas mention and
-- bring theirs (`appFactsWith`), over any applications, any that bring
-- their facts, and any that their facts mention, wherever its rounds end.
impl fact_applications: check::fact_applications for (written : List Nat) (rel : List (Nat × Nat))
    (brings : Nat → Bool) (rounds : Nat) (r : List (Nat × Unit))
    (_ends : (Fren.Core.closeApps brings (insideOf rel) rounds (written.filter brings) (written.filter brings) []).run
      = some r) {
  written := Fren.FinSet.ofList (written.map fun (a : Nat) => (a : Int)),
  inside := Fren.FinSet.ofList (rel.map fun (p : Nat × Nat) => ((p.1 : Int), (p.2 : Int))),
  brings := Fren.FinSet.ofList
    (((written ++ (rel.flatMap fun (p : Nat × Nat) => [p.1, p.2]) ++ r.map (·.1)).filter brings).map
      fun (a : Nat) => (a : Int)),
  brought := Fren.FinSet.ofList (r.map fun (p : Nat × Unit) => (p.1 : Int)),
  «closed?» := true,
} by
  intro written rel brings rounds r hr _
  obtain ⟨c1, c2, c3⟩ := closeApps_spec brings (insideOf rel) rounds _ _ [] r (fun x => by simp) (by simp) hr
  have c3 := c3 fun x h => by simp at h; exact h.2
  unfold check.fact_applications.ensures check.fact_applications.ensure.rule
  simp only [true_iff, Fren.FinSet.subset_def, Fren.FinSet.mem_inter, Fren.FinSet.mem_image, Fren.FinSet.mem_ofList,
    List.mem_map, List.mem_filter]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro x ⟨⟨a, ha, rfl⟩, ⟨b, ⟨_, hb⟩, he⟩⟩
    have : b = a := Int.ofNat_inj.mp he
    subst this
    obtain ⟨p, hp, e⟩ := List.mem_map.mp (c2 b (List.mem_filter.mpr ⟨ha, hb⟩))
    exact ⟨p, hp, by rw [e]⟩
  · rintro y ⟨⟨a, ⟨p, hp, rfl⟩, ⟨q, hq, hqe⟩⟩, ⟨b, ⟨_, hb⟩, rfl⟩⟩
    simp only [Prod.mk.injEq] at hqe
    have h1 : q.1 = p.1 := Int.ofNat_inj.mp hqe.1
    have h2 : q.2 = b := Int.ofNat_inj.mp hqe.2
    have hin : b ∈ (insideOf rel p.1).run.2 := by
      simp only [insideOf, Id.run_pure, List.mem_map, List.mem_filter, beq_iff_eq]
      exact ⟨q, ⟨hq, h1⟩, h2⟩
    obtain ⟨p', hp', e⟩ := List.mem_map.mp (c1 p hp b hin hb)
    exact ⟨p', hp', by rw [e]⟩
  · rintro x ⟨p, hp, rfl⟩
    exact ⟨p.1, ⟨List.mem_append_right _ (List.mem_map_of_mem hp), c3 p.1 (List.mem_map_of_mem hp)⟩, rfl⟩

-- Both front ends take the functions whose contracts a check rests on
-- with `checkApplies` (`itemEvidence`, `appliedOf`).
impl check_applies: check::check_applies for (q i : List Nat) (own : List Caveat) {
  queried := Fren.FinSet.ofList (q.map fun (j : Nat) => (j : Int)),
  item_applies := Fren.FinSet.ofList (i.map fun (j : Nat) => (j : Int)),
  «random?» := own.contains .random,
  applies := Fren.FinSet.ofList ((Fren.Core.checkApplies q.toArray i.toArray own).toList.map fun (j : Nat) => (j : Int)),
} by
  intro q i own _
  unfold Fren.Core.checkApplies
  cases own.contains .random <;> simp_all [fren_spec, check.check_applies.ensures]

-- Lean decides what it reports with `hostedReported`, from the caveats
-- that `passEvidence` gives each check (`itemEvidence`), each check's own
-- verdict and the caveats of its own method: Lean's stand-ins for what it
-- does not run (`hostedStandIns`) are the checks whose own caveat is
-- `Random`.
impl hosted_runs: check::hosted_runs for (cs : List (CheckEvidence Caveat)) (failed : List Nat) (k : Nat) {
  own := Fren.FinSet.ofList (ownPairs cs),
  failed := Fren.FinSet.ofList (failed.map fun (j : Nat) => (j : Int)),
  premises := Fren.FinSet.ofList (premisePairs cs),
  k := (k : Int),
  «reported?» := Fren.Core.hostedReported (((passEvidence cs)[k]?.map (·.1)).getD []) (failed.contains k)
    ((at_ cs k).own.contains .random),
} by
  intro cs failed k hA
  simp only [check.hosted_runs.assumes, check.hosted_runs.assume.in_order] at hA
  have hpe := pass_evidence cs k (by trivial)
  unfold check.pass_evidence.ensures check.pass_evidence.ensure.random_rule at hpe
  have hr := hpe.1 hA
  unfold check.hosted_runs.ensures check.hosted_runs.ensure.rule
  -- `k`'s own caveats have `Random` just where the spec's `own` does.
  have hk : (((k : Int), check.Caveat.Random) ∈ Fren.FinSet.ofList (ownPairs cs)) ↔
      (at_ cs k).own.contains .random = true := by
    rw [Fren.FinSet.mem_ofList, mem_ownPairs, List.contains_iff_mem]
    constructor
    · rintro ⟨_, c', hc', he⟩
      have : c' = .random := toCaveat_inj.mp (by simpa [toCaveat] using he)
      exact this ▸ hc'
    · intro h
      refine ⟨?_, .random, h, rfl⟩
      rcases Nat.lt_or_ge k cs.length with hl | hl
      · exact hl
      · rw [at_past cs k (by omega)] at h
        simp at h
  have hf := mem_nats failed k
  simp only [fren_spec, Fren.Core.hostedReported, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, hk, hf]
  rw [← hr]
  cases (((passEvidence cs)[k]?.map (·.1)).getD []).contains .random <;>
    cases failed.contains k <;> cases (at_ cs k).own.contains .random <;> simp

-- Both front ends report each check with `reportedPass` (`itemEvidence`).
impl reported_pass: check::reported_pass for (k : CheckKind) (v : Fren.Core.Verdict) (own cs : List Caveat) (s : Bool) {
  kind := toCheckKind k,
  verdict := toVerdict v,
  own := Fren.FinSet.ofList (own.map toCaveat),
  caveats := Fren.FinSet.ofList (cs.map toCaveat),
  «settled?» := s,
  shown := toVerdict (reportedPass v own cs s).shown,
  «by_testing?» := (reportedPass v own cs s).byTesting,
  «by_bound?» := (reportedPass v own cs s).byBound,
  «weakened?» := (reportedPass v own cs s).weakened,
  «unsettled?» := (reportedPass v own cs s).unsettled,
} by
  intro k v own cs s hA
  unfold check.reported_pass.assumes check.reported_pass.assume.own_within at hA
  have hsub := hA.1
  have hmem (cv : Caveat) (l : List Caveat) : toCaveat cv ∈ Fren.FinSet.ofList (l.map toCaveat) ↔ l.contains cv = true := by
    simp only [Fren.FinSet.mem_ofList, List.mem_map, toCaveat_inj]
    exact ⟨fun ⟨a, ha, he⟩ => he ▸ List.contains_iff_mem.mpr ha, fun h => ⟨cv, List.contains_iff_mem.mp h, rfl⟩⟩
  have hne : Fren.FinSet.ofList (cs.map toCaveat) ≠ Fren.FinSet.ofList (own.map toCaveat) ↔
      (cs.any fun c => !own.contains c) = true := by
    rw [Ne, Fren.FinSet.ext_iff]
    simp only [List.any_eq_true, Bool.not_eq_true']
    constructor
    · intro h
      apply Classical.byContradiction
      intro hall
      apply h
      intro x
      cases x with
      | Random =>
        rw [show check.Caveat.Random = toCaveat .random from rfl, hmem, hmem]
        constructor
        · intro hc
          cases e : own.contains .random
          · exact absurd ⟨.random, List.contains_iff_mem.mp hc, e⟩ hall
          · rfl
        · intro ho
          exact hsub _ ((hmem .random own).mpr ho) |> (hmem .random cs).mp
      | Bounded =>
        rw [show check.Caveat.Bounded = toCaveat .bounded from rfl, hmem, hmem]
        constructor
        · intro hc
          cases e : own.contains .bounded
          · exact absurd ⟨.bounded, List.contains_iff_mem.mp hc, e⟩ hall
          · rfl
        · intro ho
          exact hsub _ ((hmem .bounded own).mpr ho) |> (hmem .bounded cs).mp
    · rintro ⟨c, hc, hno⟩ heq
      have := (heq (toCaveat c)).mp ((hmem c cs).mpr (List.contains_iff_mem.mpr hc))
      rw [hmem] at this
      rw [this] at hno
      cases hno
  unfold check.reported_pass.ensures check.reported_pass.ensure.verdict_rule check.reported_pass.ensure.testing
    check.reported_pass.ensure.bound check.reported_pass.ensure.weakened check.reported_pass.ensure.warned
  have hR : check.Caveat.Random ∈ Fren.FinSet.ofList (cs.map toCaveat) ↔ cs.contains .random = true := hmem .random cs
  have hB : check.Caveat.Bounded ∈ Fren.FinSet.ofList (cs.map toCaveat) ↔ cs.contains .bounded = true := hmem .bounded cs
  cases v <;> cases s <;> simp (config := { decide := true }) [reportedPass, toVerdict, hR, hB, hne]

end Fren.Impls.PassEvidence
