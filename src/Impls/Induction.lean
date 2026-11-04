-- keep-sorted start
import FrenCore.Induction
import Impls.Global
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # Induction on a global expectation's parameter (`Reqs/Lang/Recursion#induction`) -/

namespace Fren.Impls

open Fren.Core (BlockMember Verdict inductionMember inductionCandidate inductionHypotheses inductionVerdict payloadsOf)

theorem inductionMember_iff (m : BlockMember) :
    inductionMember m = true ↔ toBlockMember m = .Assume ∨ toBlockMember m = .Expect ∨ toBlockMember m = .Cover := by
  cases m <;> decide

-- Both front ends decide which parameters induction is tried on with
-- `inductionCandidate`, of the kinds of the block's members.
impl induction_candidate: lang::induction_candidate for (ms : List BlockMember) (a c r d : Bool) {
  members := Fren.FinSet.ofList (ms.map toBlockMember),
  «abstract?» := a,
  «constrained?» := c,
  «recursive?» := r,
  «decreasing?» := d,
  «candidate?» := inductionCandidate ms a c r d,
} by
  intro ms a c r d
  have members : ms.all inductionMember = true ↔
      Fren.FinSet.ofList (ms.map toBlockMember) ⊆ ({.Assume, .Expect, .Cover} : Fren.FinSet lang.BlockMember) := by
    simp only [List.all_eq_true, Fren.FinSet.subset_def, Fren.FinSet.mem_ofList, List.mem_map, Fren.FinSet.mem_insert,
      Fren.FinSet.mem_singleton]
    constructor
    · rintro h _ ⟨m, hm, rfl⟩
      exact (inductionMember_iff m).mp (h m hm)
    · intro h m hm
      exact (inductionMember_iff m).mpr (h _ ⟨m, hm, rfl⟩)
  simp only [fren_spec, inductionCandidate, Bool.and_eq_true, Bool.not_eq_true', members]
  cases a <;> cases c <;> cases r <;> cases d <;> simp

-- Both front ends decide whether a parameter's type has a payload of its
-- own type with `directlyRecursive`, which compares the payloads' types at
-- the type's arguments with `payloadOfType`.
impl directly_recursive: lang::directly_recursive for (ps : List (List Nat)) (t : Nat) {
  ty := t,
  payloads := Fren.Seq.ofList (ps.map fun p => Fren.Seq.ofList (p.map Int.ofNat)),
  «recursive?» := Fren.Core.payloadOfType ps t,
} by
  intro ps t
  simp only [fren_spec]
  intro _
  have nth (k : Int) (k0 : 0 ≤ k) (k1 : k < ps.length) :
      (Fren.Seq.ofList (ps.map fun p => Fren.Seq.ofList (p.map Int.ofNat))).nth k
        = Fren.Seq.ofList ((ps[k.toNat]'(by omega)).map Int.ofNat) := by
    rw [Fren.Seq.nth_of_lt _ _ k0 (by simpa using k1)]
    simp
  simp only [Fren.Core.payloadOfType, List.any_eq_true, List.contains_iff_mem, Fren.Seq.len_eq, Fren.Seq.toList_ofList,
    List.length_map]
  constructor
  · rintro ⟨p, hp, ht⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hp
    refine ⟨k, ⟨by omega, by omega⟩, ?_⟩
    rw [nth k (by omega) (by omega)]
    simp only [Fren.Seq.mem_iff, Fren.Seq.toList_ofList, List.mem_map]
    exact ⟨t, by simpa using ht, rfl⟩
  · rintro ⟨k, ⟨k0, k1⟩, ht⟩
    rw [nth k k0 k1] at ht
    simp only [Fren.Seq.mem_iff, Fren.Seq.toList_ofList, List.mem_map] at ht
    obtain ⟨a, ha, e⟩ := ht
    have hk : k.toNat < ps.length := by omega
    exact ⟨ps[k.toNat], List.getElem_mem hk, (Int.ofNat_inj.mp e) ▸ ha⟩

/-! ## The hypotheses -/

theorem mem_payloadsOf {T : Type} [BEq T] [LawfulBEq T] (n : Nat) (payloads : List T) (t : T) (c : Nat) :
    c ∈ payloadsOf n payloads t ↔ ∃ k, ∃ hk : k < payloads.length, c = n + k ∧ payloads[k] = t := by
  simp only [payloadsOf, List.mem_map, List.mem_filter, beq_iff_eq, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨x, k⟩, ⟨hk, hx⟩, rfl⟩
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hk
    exact ⟨k, hlt, rfl, hget ▸ hx⟩
  · rintro ⟨k, hk, rfl, hx⟩
    exact ⟨(payloads[k], k), ⟨List.getElem?_eq_getElem hk, hx⟩, rfl⟩

/-- A payload's position among the case's variables, whose types are
`params ++ payloads`. -/
theorem mem_payloadsOf_append {T : Type} [BEq T] [LawfulBEq T] (params payloads : List T) (t : T) (c : Nat) :
    c ∈ payloadsOf params.length payloads t ↔
      params.length ≤ c ∧ c < params.length + payloads.length ∧ (params ++ payloads)[c]? = some t := by
  rw [mem_payloadsOf]
  constructor
  · rintro ⟨k, hk, rfl, hx⟩
    refine ⟨by omega, by omega, ?_⟩
    rw [List.getElem?_append_right (by omega)]
    simp [hk, hx]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨c - params.length, by omega, by omega, ?_⟩
    rw [List.getElem?_append_right h1] at h3
    exact (List.getElem?_eq_some_iff.mp h3).2

/-- The applications of `inductionHypotheses`: each child's, with the
parameters elsewhere. -/
theorem mem_inductionHypotheses {T : Type} [BEq T] [LawfulBEq T] (params payloads : List T) (i : Nat)
    (hi : i < params.length) (h : List Nat) :
    h ∈ inductionHypotheses params i payloads ↔ ∃ c, (params.length ≤ c ∧ c < params.length + payloads.length ∧
      (params ++ payloads)[c]? = some params[i]) ∧ h = (List.range params.length).set i c := by
  simp only [inductionHypotheses, List.getElem?_eq_getElem hi, List.mem_map, mem_payloadsOf_append]
  constructor <;> rintro ⟨c, hc, e⟩ <;> exact ⟨c, hc, e.symm⟩

theorem getElem_set_range (n i c j : Nat) (hj : j < n) :
    ((List.range n).set i c)[j]'(by simpa using hj) = if i = j then c else j := by
  rw [List.getElem_set]
  split <;> simp_all

theorem nth_ofList_map (l : List Nat) (x : Int) (h0 : 0 ≤ x) (h1 : x < l.length) :
    (Fren.Seq.ofList (l.map Int.ofNat)).nth x = ((l[x.toNat]'(by omega) : Nat) : Int) := by
  rw [Fren.Seq.nth_of_lt _ _ h0 (by simpa using h1)]
  simp

-- Both front ends generate each case's recursive applications with
-- `inductionHypotheses`, of the types of the parameters and of the
-- variant's payloads, here numbered.
impl induction_hypotheses: lang::induction_hypotheses for (params payloads : List Nat) (i : Int) {
  types := Fren.Seq.ofList ((params ++ payloads).map Int.ofNat),
  n_params := params.length,
  induction_on := i,
  hypotheses := Fren.FinSet.ofList ((inductionHypotheses params i.toNat payloads).map fun h =>
    Fren.Seq.ofList (h.map Int.ofNat)),
  «generated?» := true,
} by
  intro params payloads i
  simp only [fren_spec]
  intro ⟨⟨h0, h1⟩, _⟩
  have hN : i.toNat < params.length := by omega
  have hi : (i.toNat : Int) = i := Int.toNat_of_nonneg h0
  have hlen : (Fren.Seq.ofList (List.map Int.ofNat (params ++ payloads))).len = params.length + payloads.length := by
    simp
  -- The type of a parameter, as the case's variables give it.
  have param (j : Nat) (hj : j < params.length) :
      (params ++ payloads)[j]'(by simp; omega) = params[j] := List.getElem_append_left hj
  simp only [hlen, true_iff, Fren.FinSet.mem_ofList, List.mem_map, mem_inductionHypotheses params payloads _ hN]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨h, ⟨c, ⟨c1, c2, c3⟩, rfl⟩, rfl⟩
    have at_i : (Fren.Seq.ofList (((List.range params.length).set i.toNat c).map Int.ofNat)).nth i = c := by
      rw [nth_ofList_map _ _ h0 (by simp; omega)]
      simp [getElem_set_range _ _ _ _ hN]
    rw [at_i]
    refine ⟨⟨⟨by simp, by omega, by omega⟩, ?_⟩, ?_⟩
    · rw [nth_ofList_map _ _ (by omega) (by simp; omega), nth_ofList_map _ _ h0 (by simp; omega)]
      obtain ⟨_, e⟩ := List.getElem?_eq_some_iff.mp c3
      simp only [Int.toNat_natCast, e, param _ hN]
    · rintro j ⟨⟨j0, j1⟩, ji⟩
      rw [nth_ofList_map _ _ j0 (by simp; omega)]
      have : i.toNat ≠ j.toNat := by omega
      simp [getElem_set_range _ _ _ _ (show j.toNat < params.length by omega), this]
      omega
  · rintro c ⟨⟨c1, c2⟩, ct⟩
    rw [nth_ofList_map _ _ (by omega) (by simp; omega), nth_ofList_map _ _ h0 (by simp; omega)] at ct
    have ct := Int.ofNat_inj.mp ct
    refine ⟨_, ⟨_, ⟨c.toNat, ⟨by omega, by omega, ?_⟩, rfl⟩, rfl⟩, ?_⟩
    · rw [List.getElem?_eq_getElem (by simp; omega), ct, param _ hN]
    · rw [nth_ofList_map _ _ h0 (by simp; omega)]
      simp [getElem_set_range _ _ _ _ hN]
      omega

def toRecPost : Verdict → lang.RecPost
  | .pass => .Passed
  | .fail => .Failed
  | .inconclusive => .Inconclusive

instance : LawfulBEq Verdict where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

theorem toRecPost_passed (v : Verdict) : toRecPost v = .Passed ↔ v = .pass := by
  cases v <;> simp [toRecPost]

theorem some_passed (as : List Verdict) :
    (∃ k : Int, (0 ≤ k ∧ k < (Fren.Seq.ofList (as.map toRecPost)).len) ∧
      (Fren.Seq.ofList (as.map toRecPost)).nth k = .Passed) ↔ as.contains .pass = true := by
  rw [List.contains_iff_mem, List.mem_iff_getElem]
  constructor
  · rintro ⟨k, ⟨k0, k1⟩, hk⟩
    simp only [Fren.Seq.len_eq, Fren.Seq.toList_ofList, List.length_map] at k1
    rw [Fren.Seq.nth_of_lt _ _ k0 (by simpa using k1)] at hk
    simp only [Fren.Seq.toList_ofList, List.getElem_map, toRecPost_passed] at hk
    exact ⟨k.toNat, by omega, hk⟩
  · rintro ⟨k, hk, e⟩
    refine ⟨k, ⟨by omega, by simpa using hk⟩, ?_⟩
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using hk)]
    simp [e, toRecPost]

-- Both front ends report what `inductionVerdict` gives, of the claim's own
-- verdict and those of the inductions tried, in order.
impl induction_verdict: lang::induction_verdict for (d : Verdict) (r : Bool) (as : List Verdict) {
  direct := toRecPost d,
  «refuted?» := r,
  attempts := Fren.Seq.ofList (as.map toRecPost),
  reported := toRecPost (inductionVerdict d r as),
} by
  intro d r as
  simp only [fren_spec, some_passed]
  intro _
  cases d <;> cases r <;> by_cases h : Verdict.pass ∈ as <;>
    simp (config := { decide := true }) [inductionVerdict, toRecPost, h]

end Fren.Impls
