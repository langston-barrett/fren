-- keep-sorted start
import FrenCore.FnBlocks
import FrenCore.Procedures
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # The migration from components to procedures (`Reqs/Lang/Procedures#migration`) -/

namespace Fren.Impls

open Fren.Core (OldMember Placement argumentOrder paramsOf placement resultsOf)

def toOldMember : OldMember → lang.OldMember
  | .input => .Input
  | .output .. => .Output
  | .other => .Other

def toPlacement : Placement → lang.Placement
  | .param => .Param
  | .result => .Result
  | .resultDefined => .ResultDefined
  | .exists => .Exists
  | .let => .Let
  | .kept => .Kept

-- For every member of a component: where `fren fix` puts it.
impl migrated_member: lang::migrated_member for (m : OldMember) {
  member := toOldMember m,
  pub? := (match m with | .output p _ _ => p | _ => false),
  defined? := (match m with | .output _ _ d => d | _ => false),
  placement := toPlacement (placement m),
} by
  intro m _
  cases m with
  | input | other => simp [fren_spec, toOldMember, toPlacement, placement]
  | output p e d => cases p <;> cases d <;> simp [fren_spec, toOldMember, toPlacement, placement]

/-- A member of a component, as `lang::migrated_params` classifies it. -/
def memberKindOf : OldMember → lang.Kind
  | .input => .Input
  | .output true _ _ => .PublicOutput
  | _ => .Other

/-! ## Lemmas for the migration's impls -/

theorem nth_ofList {α : Type} [Inhabited α] (l : List α) (i : Int) (h0 : 0 ≤ i) (h1 : i < l.length) :
    (Fren.Seq.ofList l).nth i = l[i.toNat]'(by omega) := by
  simp [Fren.Seq.nth_of_lt, h0, h1]

theorem nth_ofList_map_ofNat (l : List Nat) (i : Int) (h0 : 0 ≤ i) (h1 : i < l.length) :
    (Fren.Seq.ofList (l.map Int.ofNat)).nth i = (l[i.toNat]'(by omega) : Int) := by
  rw [nth_ofList _ _ h0 (by simpa using h1)]
  simp

/-- One half of `lang::migrated_params`, for the members of kind `K` at
the positions `L`. -/
theorem migrated_part (ms : List OldMember) (K : lang.Kind) (L : List Nat)
    (hmem : ∀ i (h : i < ms.length), memberKindOf ms[i] = K ↔ i ∈ L)
    (hlt : ∀ x ∈ L, x < ms.length) (hs : L.Pairwise (· < ·)) :
    ((∀ k : Int, 0 ≤ k → k < (L.length : Int) →
        (0 ≤ (Fren.Seq.ofList (L.map Int.ofNat)).nth k ∧
          (Fren.Seq.ofList (L.map Int.ofNat)).nth k < (ms.length : Int)) ∧
        (Fren.Seq.ofList (ms.map memberKindOf)).nth ((Fren.Seq.ofList (L.map Int.ofNat)).nth k) = K) ∧
      ∀ j k : Int, 0 ≤ j → j < (L.length : Int) → 0 ≤ k → k < (L.length : Int) → j < k →
        (Fren.Seq.ofList (L.map Int.ofNat)).nth j < (Fren.Seq.ofList (L.map Int.ofNat)).nth k) ∧
    ∀ m : Int, 0 ≤ m → m < (ms.length : Int) →
      (Fren.Seq.ofList (ms.map memberKindOf)).nth m = K → ∃ a, a ∈ L ∧ (a : Int) = m := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro k h0 h1
    have hk : k.toNat < L.length := by omega
    have hx := hlt _ (List.getElem_mem hk)
    rw [nth_ofList_map_ofNat L k h0 h1]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [nth_ofList _ _ (by omega) (by simpa using hx)]
    simpa using (hmem _ hx).2 (List.getElem_mem hk)
  · intro j k h0 hj1 hk0 h1 hjk
    rw [nth_ofList_map_ofNat L j h0 hj1, nth_ofList_map_ofNat L k hk0 h1]
    have := List.pairwise_iff_getElem.1 hs j.toNat k.toNat (by omega) (by omega) (by omega)
    omega
  · intro m h0 h1 hK
    rw [nth_ofList _ _ h0 (by simpa using h1)] at hK
    exact ⟨m.toNat, (hmem m.toNat (by omega)).1 (by simpa using hK), by omega⟩

theorem mem_filter_range {n : Nat} {q : Nat → Bool} {x : Nat} :
    x ∈ (List.range n).filter q ↔ x < n ∧ q x = true := by
  simp

theorem pairwise_filter_range (n : Nat) (q : Nat → Bool) : ((List.range n).filter q).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter q

theorem count_eq_one_iff (p : String) : ∀ bs : List String,
    bs.count p = 1 ↔ ∃ i, ∃ h : i < bs.length, bs[i] = p ∧ ∀ j (hj : j < bs.length), bs[j] = p → j = i
  | [] => by simp
  | b :: bs => by
    rw [List.count_cons]
    by_cases hb : b = p
    · subst hb
      simp only [beq_self_eq_true, if_true, Nat.add_eq_right]
      constructor
      · intro h0
        refine ⟨0, by simp, rfl, ?_⟩
        intro j hj hjb
        cases j with
        | zero => rfl
        | succ j =>
          exfalso
          simp at hjb
          exact (List.count_eq_zero.1 h0) (hjb ▸ List.getElem_mem _)
      · rintro ⟨i, hi, _, hu⟩
        apply List.count_eq_zero.2
        intro hm
        obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hm
        have h1 := hu (j + 1) (by simp; omega) (by simpa using hjb)
        have h2 := hu 0 (by simp) rfl
        omega
    · have hb' : (b == p) = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, if_false, Nat.add_zero]
      rw [count_eq_one_iff p bs]
      constructor
      · rintro ⟨i, hi, hbi, hu⟩
        refine ⟨i + 1, by simp; omega, by simpa using hbi, ?_⟩
        intro j hj hjb
        cases j with
        | zero => exact absurd hjb hb
        | succ j =>
          have := hu j (by simp at hj; omega) (by simpa using hjb)
          omega
      · rintro ⟨i, hi, hbi, hu⟩
        cases i with
        | zero => exact absurd hbi hb
        | succ i =>
          refine ⟨i, by simp at hi; omega, by simpa using hbi, ?_⟩
          intro j hj hjb
          have := hu (j + 1) (by simp; omega) (by simpa using hjb)
          omega

theorem filter_zipIdx_length (p : String) : ∀ (bs : List String) (s : Nat),
    ((bs.zipIdx s).filter (·.1 == p)).length = bs.count p
  | [], _ => by simp
  | b :: bs, s => by
    rw [List.zipIdx_cons, List.filter_cons, List.count_cons, ← filter_zipIdx_length p bs (s + 1)]
    by_cases hb : b = p <;> simp [hb]

theorem find_zipIdx (p : String) : ∀ (bs : List String) (s : Nat), p ∈ bs →
    ∃ i, ∃ h : i < bs.length, bs[i] = p ∧ (bs.zipIdx s).find? (·.1 == p) = some (p, s + i)
  | [], _, h => by simp at h
  | b :: bs, s, h => by
    by_cases hb : b = p
    · subst hb
      exact ⟨0, by simp, rfl, by simp⟩
    · have hm : p ∈ bs := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hb
        · exact h
      obtain ⟨i, hi, hbi, hf⟩ := find_zipIdx p bs (s + 1) hm
      refine ⟨i + 1, by simp; omega, by simpa using hbi, ?_⟩
      rw [List.zipIdx_cons, List.find?_cons]
      have hb' : (b == p) = false := by simpa using hb
      simp only [hb', hf]
      congr 2
      omega

theorem mapM_some {α β : Type} (f : α → Option β) : ∀ l : List α, (∀ x ∈ l, (f x).isSome) →
    ∃ r, l.mapM f = some r ∧ ∃ hr : r.length = l.length, ∀ k (h : k < l.length), f l[k] = some (r[k]'(by omega))
  | [], _ => ⟨[], by simp, by simp, by simp⟩
  | x :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h x (by simp))
    obtain ⟨r, hr, hlen, hk⟩ := mapM_some f l (fun y hy => h y (by simp [hy]))
    refine ⟨b :: r, by simp [hb, hr], by simp [hlen], ?_⟩
    intro k hk'
    cases k with
    | zero => simpa using hb
    | succ k => simpa using hk k (by simp at hk'; omega)

theorem fixed_iff (ps bs : List String) :
    (bs.length = ps.length ∧ ∀ p ∈ ps, bs.count p = 1) ↔
    ((bs.length : Int) = ps.length ∧ ∀ k : Int, 0 ≤ k → k < (ps.length : Int) →
      ∃ i : Int, ((0 ≤ i ∧ i < (bs.length : Int)) ∧ (Fren.Seq.ofList bs).nth i = (Fren.Seq.ofList ps).nth k) ∧
        ∀ j : Int, 0 ≤ j → j < (bs.length : Int) → (Fren.Seq.ofList bs).nth j = (Fren.Seq.ofList ps).nth k → j = i) := by
  constructor
  · rintro ⟨hl, hc⟩
    refine ⟨by omega, ?_⟩
    intro k h0 h1
    rw [nth_ofList ps k h0 h1]
    obtain ⟨i, hi, hbi, hu⟩ := (count_eq_one_iff _ bs).1 (hc _ (List.getElem_mem _))
    refine ⟨i, ⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
    · rw [nth_ofList bs i (by omega) (by omega)]
      simpa using hbi
    · intro j hj0 hj1 hj
      rw [nth_ofList bs j hj0 hj1] at hj
      have := hu j.toNat (by omega) hj
      omega
  · rintro ⟨hl, h⟩
    refine ⟨by omega, ?_⟩
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨i, ⟨⟨hi0, hi1⟩, hbi⟩, hu⟩ := h k (by omega) (by omega)
    rw [nth_ofList ps k (by omega) (by omega)] at hbi hu
    rw [nth_ofList bs i hi0 hi1] at hbi
    apply (count_eq_one_iff _ bs).2
    refine ⟨i.toNat, by omega, by simpa using hbi, ?_⟩
    intro j hj hjb
    have := hu j (by omega) (by omega) (by rw [nth_ofList bs j (by omega) (by omega)]; simpa using hjb)
    omega

theorem argumentOrder_cond (ps bs : List String) :
    (bs.zipIdx.length == ps.length && ps.all fun p => (bs.zipIdx.filter (·.1 == p)).length == 1) = true ↔
    (bs.length = ps.length ∧ ∀ p ∈ ps, bs.count p = 1) := by
  simp [filter_zipIdx_length]

-- For every component's members: the parameters and results `fren fix`
-- writes, as their members' positions.
impl migrated_params: lang::migrated_params for (ms : List OldMember) {
  members := Fren.Seq.ofList (ms.map memberKindOf),
  params := Fren.Seq.ofList ((paramsOf ms).map Int.ofNat),
  results := Fren.Seq.ofList ((resultsOf ms).map Int.ofNat),
  written? := true,
} by
  intro ms _
  simp [fren_spec]
  have hp : ∀ i (h : i < ms.length), memberKindOf ms[i] = .Input ↔ i ∈ paramsOf ms := by
    intro i h
    simp only [paramsOf, mem_filter_range, List.getElem?_eq_getElem h]
    generalize ms[i] = x
    rcases x with _ | ⟨_ | _, _, _⟩ | _ <;> simp [memberKindOf, h] <;> rfl
  have hr : ∀ i (h : i < ms.length), memberKindOf ms[i] = .PublicOutput ↔ i ∈ resultsOf ms := by
    intro i h
    simp only [resultsOf, mem_filter_range, List.getElem?_eq_getElem h]
    generalize ms[i] = x
    rcases x with _ | ⟨_ | _, _, _⟩ | _ <;> simp [memberKindOf, h] <;> rfl
  obtain ⟨⟨a, b⟩, c⟩ := migrated_part ms .Input (paramsOf ms) hp
    (fun x hx => (mem_filter_range.1 hx).1) (pairwise_filter_range _ _)
  obtain ⟨⟨d, e⟩, f⟩ := migrated_part ms .PublicOutput (resultsOf ms) hr
    (fun x hx => (mem_filter_range.1 hx).1) (pairwise_filter_range _ _)
  exact ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩

-- For every instance: the order of its fix's arguments, as the positions
-- of its bindings, which `fren fix` reads the arguments' text from.
impl argument_order: lang::argument_order for (ps bs : List String) {
  params := Fren.Seq.ofList ps,
  bound := Fren.Seq.ofList bs,
  positions := Fren.Seq.ofList (((argumentOrder ps (bs.zipIdx)).getD []).map Int.ofNat),
  fixed? := (argumentOrder ps (bs.zipIdx)).isSome,
  written? := true,
} by
  intro ps bs _
  simp [fren_spec]
  by_cases hP : bs.length = ps.length ∧ ∀ p ∈ ps, bs.count p = 1
  · obtain ⟨hl, hc⟩ := hP
    have hs : ∀ p ∈ ps, ((bs.zipIdx.find? (·.1 == p)).map (·.2)).isSome := by
      intro p hp
      obtain ⟨i, _, _, hf⟩ := find_zipIdx p bs 0 (List.count_pos_iff.1 (by rw [hc p hp]; omega))
      simp [hf]
    obtain ⟨r, hr, hlen, hk⟩ := mapM_some _ ps hs
    have hA : argumentOrder ps bs.zipIdx = some r := by
      unfold argumentOrder
      rw [if_pos ((argumentOrder_cond ps bs).2 ⟨hl, hc⟩)]
      exact hr
    rw [hA]
    simp only [Option.isSome_some, Option.getD_some, if_true, true_iff]
    refine ⟨(fixed_iff ps bs).1 ⟨hl, hc⟩, by simp [hlen], ?_⟩
    intro k h0 h1
    have hk' : k.toNat < ps.length := by omega
    obtain ⟨i, hi, hbi, hf⟩ := find_zipIdx ps[k.toNat] bs 0
      (List.count_pos_iff.1 (by rw [hc _ (List.getElem_mem hk')]; omega))
    have hri := hk k.toNat hk'
    rw [hf] at hri
    simp only [Option.map_some, Option.some.injEq, Nat.zero_add] at hri
    rw [nth_ofList_map_ofNat r k h0 (by omega), ← hri, nth_ofList bs i (by omega) (by omega),
      nth_ofList ps k h0 h1]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    simpa using hbi
  · have hA : argumentOrder ps bs.zipIdx = none := by
      unfold argumentOrder
      rw [if_neg (fun h => hP ((argumentOrder_cond ps bs).1 h))]
    rw [hA]
    simp only [Option.isSome_none, Option.getD_none, Bool.false_eq_true, false_iff, if_false]
    exact ⟨fun h => hP ((fixed_iff ps bs).2 h), rfl⟩

/-! ## Function blocks (`Reqs/Lang/Items#function-blocks`) -/

def toFnMemberKind : Fren.Core.FnMember → lang.FnMemberKind
  | .use => .Use
  | .assumption => .Assumption
  | .exists => .Exists
  | .let => .Let
  | .define => .Define
  | .call => .Call
  | .guarantee => .Guarantee
  | .claim => .Claim
  | .evidence => .Evidence

def toFnVerdict : Fren.Core.FnVerdict → lang.FnVerdict
  | .accepted => .Accepted
  | .notFunctions => .NotFunctions
  | .notYet => .NotYet

-- For every member of a function's block, written `det` or not: whether
-- the block takes it, as both front ends decide it.
impl fn_member: lang::fn_member for (m : Fren.Core.FnMember) (d : Bool) {
  member := toFnMemberKind m,
  det? := d,
  verdict := toFnVerdict (Fren.Core.fnMemberVerdict m d),
} by
  intro m d _
  cases m <;> cases d <;> simp [fren_spec, toFnMemberKind, toFnVerdict, Fren.Core.fnMemberVerdict]

end Fren.Impls
