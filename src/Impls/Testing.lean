-- keep-sorted start
import Fren.Impl
import Fren.Trace
import FrenTest.Jobs
import FrenTest.Ui
import Reqs.Testing
-- keep-sorted end
open Fren.Lang

/-! # The test driver (`Reqs/dev/Testing`)

`testing::shard`, proved of `FrenTest.Jobs.placement`, by which
`FrenTest.Jobs.selectJobs` selects the jobs of a shard, for any jobs; and
`testing::ui_file`, proved of `FrenTest.Ui.check`, for any messages and
expectations: its search, `assignable`, finds a way to give the
expectations messages exactly when there is one (`assignable_iff`).
`testing::fresh` rests on Lake, so it is trusted. -/

namespace Fren.Impls.Testing

open FrenTest.Jobs

/-- The jobs as `testing::shard` has them. -/
def toJobs (jobs : List (List String)) : Fren.Seq (Fren.Seq String) := Fren.Seq.ofList (jobs.map Fren.Seq.ofList)

theorem ownMutantsJob_iff (j : List String) : ownMutantsJob j = true ↔ ∃ c d, j = ["mutation", "0", c, d] := by
  unfold ownMutantsJob; split <;> simp_all

theorem own_mutants_iff (j : List String) : testing.own_mutants? (Fren.Seq.ofList j) = ownMutantsJob j := by
  rw [Bool.eq_iff_iff, ownMutantsJob_iff]
  rcases j with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩⟩ <;>
    simp [Fren.Seq.len, Fren.Seq.nth, Fren.Str.lit] <;> omega

theorem nth_toJobs (jobs : List (List String)) (i : Nat) (h : i < jobs.length) :
    (toJobs jobs).nth (i : Int) = Fren.Seq.ofList jobs[i] := by
  rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simp [toJobs]; omega)]
  simp [toJobs]

theorem skipped_iff (jobs : List (List String)) (skip : Bool) (i : Nat) (h : i < jobs.length) :
    testing.skipped? ((toJobs jobs).nth (i : Int)) skip = skipped skip jobs[i] := by
  rw [nth_toJobs jobs i h]
  simp only [testing.skipped?, own_mutants_iff, skipped]
  cases skip <;> simp

theorem countP_take_eq_zero (p : α → Bool) (l : List α) (i : Nat) :
    (l.take i).countP p = 0 ↔ ∀ h (hh : h < l.length), h < i → p l[h] = false := by
  rw [List.countP_eq_zero]
  constructor
  · intro H h hh hi
    have := H l[h] (List.mem_iff_getElem.mpr ⟨h, by simp; omega, by simp⟩)
    simpa using this
  · intro H x hx
    obtain ⟨h, hh, rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [List.length_take] at hh
    rw [List.getElem_take]
    simpa using H h (by omega) (by omega)

theorem first_kept_iff (jobs : List (List String)) (skip : Bool) (i : Nat) (h : i < jobs.length) :
    testing.first_kept? (toJobs jobs) skip (i : Int) = true ↔
      (jobs.take i).countP (!skipped skip ·) = 0 := by
  rw [countP_take_eq_zero]
  have hs : ∀ k (hk : k < jobs.length),
      testing.skipped? ((toJobs jobs).nth (k : Int)) skip = true ↔ skipped skip jobs[k] = true :=
    fun k hk => by rw [skipped_iff jobs skip k hk]
  simp only [testing.first_kept?, decide_eq_true_eq]
  simp only [testing.skipped?, testing.own_mutants?, decide_eq_true_eq] at hs
  constructor
  · intro H k hk hki
    have := (hs k hk).mp (H k ⟨by omega, by omega⟩)
    simp [this]
  · intro H k ⟨h0, hk⟩
    have e : k = ((k.toNat : Nat) : Int) := by omega
    rw [e]
    exact (hs k.toNat (by omega)).mpr (by simpa using H k.toNat (by omega) (by omega))

theorem shardOf_lt (n c : Nat) (h : 1 ≤ n) : shardOf n c < n := by
  unfold shardOf
  split
  · omega
  · split
    · omega
    · have := Nat.mod_lt (c - 1) (show n - 1 > 0 by omega); omega

theorem shardOf_eq_zero (n c : Nat) (h : 2 ≤ n) : shardOf n c = 0 ↔ c = 0 := by
  unfold shardOf
  split
  · omega
  · split <;> simp_all

-- The code gives the job at `i` its shard, `placement`, by its position
-- among the jobs kept, which is what `first_kept?` is about.
impl job_shard: testing::shard for (jobs : List (List String)) (skip : Bool) (n i : Nat) {
  jobs := toJobs jobs,
  skip? := skip,
  n := (n : Int),
  i := (i : Int),
  runs? := (placement skip n jobs i).isSome,
  k := match placement skip n jobs i with
    | some k => (k : Int)
    | none => -1,
} by
  intro jobs skip n i ⟨hn, _, hi⟩
  simp only [toJobs, Fren.Seq.len_eq, Fren.Seq.toList_ofList, List.length_map] at hi
  have hn : 1 ≤ n := by omega
  have hi : i < jobs.length := by omega
  refine ⟨?_, ?_, ?_⟩
  · show (placement skip n jobs i).isSome = true ↔ ¬testing.skipped? ((toJobs jobs).nth (i : Int)) skip = true
    rw [skipped_iff jobs skip i hi, placement, getElem!_pos jobs i hi]
    split <;> simp_all
  · show (if (placement skip n jobs i).isSome = true then _ else _)
    unfold placement
    rw [getElem!_pos jobs i hi]
    split
    · simp
    · have := shardOf_lt n ((jobs.take i).countP (!skipped skip ·)) hn
      simp; omega
  · show (placement skip n jobs i).isSome = true ∧ (n : Int) ≥ 2 → _
    rintro ⟨hs, h2⟩
    rw [first_kept_iff jobs skip i hi]
    have e := shardOf_eq_zero n ((jobs.take i).countP (!skipped skip ·)) (by omega)
    unfold placement at hs ⊢
    rw [getElem!_pos jobs i hi] at hs ⊢
    cases hsk : skipped skip jobs[i]
    · simp only [Bool.false_eq_true, if_false]
      constructor <;> intro h <;> omega
    · simp [hsk] at hs

/-! ## Expectations -/

section Matching

open FrenTest.Ui

variable (fe : String)

/-- `a` gives each expectation of `es` the position of a message of `ds`
that meets it, or -1 where it may lack one, a different message for each,
and every message to one: `testing::assigns?`, over lists. -/
def Assigns (es : List Expectation) (ds : List Diagnostic) (a : List Int) : Prop :=
  a.length = es.length ∧
  (∀ (i : Nat) (e : Expectation) (x : Int), es[i]? = some e → a[i]? = some x →
    if x = -1 then mayLack fe e = true else ∃ d, 0 ≤ x ∧ ds[x.toNat]? = some d ∧ meets fe e d = true) ∧
  (∀ (i j : Nat) (x y : Int), i < j → a[i]? = some x → a[j]? = some y → x ≠ -1 → x ≠ y) ∧
  (∀ m : Nat, m < ds.length → ∃ i : Nat, a[i]? = some (m : Int))

/-- A position of the messages after the one at `p` is erased, as it was
before; -1 stays -1. -/
def up (p : Nat) (x : Int) : Int := if x < p then x else x + 1

/-- A position of the messages, other than `p`, after the one at `p` is
erased; -1 stays -1. -/
def down (p : Nat) (x : Int) : Int := if x < p then x else x - 1

theorem assigns_nil (ds : List Diagnostic) (a : List Int) : Assigns fe [] ds a ↔ a = [] ∧ ds = [] := by
  constructor
  · rintro ⟨hl, -, -, ho⟩
    have ha : a = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    refine ⟨ha, ?_⟩
    cases ds with
    | nil => rfl
    | cons d ds =>
      obtain ⟨i, hi⟩ := ho 0 (by simp)
      simp [ha] at hi
  · rintro ⟨rfl, rfl⟩
    refine ⟨rfl, ?_, ?_, ?_⟩ <;> intros <;> simp_all

theorem assigns_skip (e : Expectation) (es : List Expectation) (ds : List Diagnostic) (a : List Int)
    (hl : mayLack fe e = true) (ha : Assigns fe es ds a) : Assigns fe (e :: es) ds (-1 :: a) := by
  obtain ⟨hlen, hg, hd, ho⟩ := ha
  refine ⟨by simp [hlen], ?_, ?_, ?_⟩
  · intro i e' x he hx
    cases i with
    | zero => simp at he hx; subst he; subst hx; simpa using hl
    | succ i => simp at he hx; exact hg i e' x he hx
  · intro i j x y hij hx hy hx1
    cases i with
    | zero => simp at hx; exact absurd hx.symm hx1
    | succ i =>
      cases j with
      | zero => omega
      | succ j => simp at hx hy; exact hd i j x y (by omega) hx hy hx1
  · intro m hm
    obtain ⟨i, hi⟩ := ho m hm
    exact ⟨i + 1, by simpa using hi⟩

theorem assigns_take (e : Expectation) (es : List Expectation) (ds : List Diagnostic) (a : List Int)
    (p : Nat) (hp : p < ds.length) (hm : meets fe e ds[p] = true) (ha : Assigns fe es (ds.eraseIdx p) a) :
    Assigns fe (e :: es) ds ((p : Int) :: a.map (up p)) := by
  obtain ⟨hlen, hg, hd, ho⟩ := ha
  refine ⟨by simp [hlen], ?_, ?_, ?_⟩
  · intro i e' x he hx
    cases i with
    | zero =>
      simp at he hx; subst he; subst hx
      rw [if_neg (by omega)]
      exact ⟨ds[p], by omega, by simp [hp], hm⟩
    | succ i =>
      simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at he hx
      obtain ⟨y, hy, rfl⟩ := hx
      have := hg i e' y he hy
      unfold up
      by_cases hy1 : y = -1
      · subst hy1
        rw [if_pos (show (-1 : Int) < p by omega)]
        simpa using this
      · rw [if_neg hy1] at this
        obtain ⟨d, h0, hdd, hmd⟩ := this
        rw [List.getElem?_eraseIdx] at hdd
        split at hdd
        · rw [if_pos (show y < (p : Int) by omega), if_neg hy1]; exact ⟨d, h0, hdd, hmd⟩
        · rw [if_neg (show ¬y < (p : Int) by omega), if_neg (show ¬y + 1 = -1 by omega)]
          refine ⟨d, by omega, ?_, hmd⟩
          rw [show (y + 1).toNat = y.toNat + 1 by omega]; exact hdd
  · intro i j x y hij hx hy hx1
    cases j with
    | zero => omega
    | succ j =>
      simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      cases i with
      | zero =>
        simp at hx; subst hx; unfold up; split <;> omega
      | succ i =>
        simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hx
        obtain ⟨w, hw, rfl⟩ := hx
        have hw1 : w ≠ -1 := by intro h; subst h; unfold up at hx1; split at hx1 <;> omega
        have := hd i j w z (by omega) hw hz hw1
        unfold up; split <;> split <;> omega
  · intro m hm
    have hl : (ds.eraseIdx p).length = ds.length - 1 := List.length_eraseIdx_of_lt hp
    rcases Nat.lt_trichotomy m p with h | h | h
    · obtain ⟨i, hi⟩ := ho m (by omega)
      refine ⟨i + 1, ?_⟩
      simp only [List.getElem?_cons_succ, List.getElem?_map, hi, Option.map_some]
      unfold up; rw [if_pos (by omega)]
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨i, hi⟩ := ho (m - 1) (by omega)
      refine ⟨i + 1, ?_⟩
      simp only [List.getElem?_cons_succ, List.getElem?_map, hi, Option.map_some]
      unfold up; rw [if_neg (by omega)]; congr 1; omega

theorem assigns_cons (e : Expectation) (es : List Expectation) (ds : List Diagnostic) (x : Int) (a : List Int)
    (ha : Assigns fe (e :: es) ds (x :: a)) :
    (mayLack fe e = true ∧ Assigns fe es ds a) ∨
      (∃ p, ∃ hp : p < ds.length, meets fe e ds[p] = true ∧ Assigns fe es (ds.eraseIdx p) (a.map (down p))) := by
  obtain ⟨hlen, hg, hd, ho⟩ := ha
  have h0 := hg 0 e x (by simp) (by simp)
  by_cases hx : x = -1
  · subst hx
    rw [if_pos rfl] at h0
    refine .inl ⟨h0, by simpa using hlen, ?_, ?_, ?_⟩
    · intro i e' y he hy; exact hg (i + 1) e' y (by simpa using he) (by simpa using hy)
    · intro i j y z hij hy hz hy1; exact hd (i + 1) (j + 1) y z (by omega) (by simpa using hy) (by simpa using hz) hy1
    · intro m hm
      obtain ⟨i, hi⟩ := ho m hm
      cases i with
      | zero => simp at hi
      | succ i => exact ⟨i, by simpa using hi⟩
  · rw [if_neg hx] at h0
    obtain ⟨d, hx0, hdx, hmd⟩ := h0
    have hp : x.toNat < ds.length := by
      have := (List.getElem?_eq_some_iff.mp hdx).1; omega
    have hdx' : ds[x.toNat] = d := (List.getElem?_eq_some_iff.mp hdx).2
    have hl : (ds.eraseIdx x.toNat).length = ds.length - 1 := List.length_eraseIdx_of_lt hp
    -- No other expectation has the message at `x`.
    have hne : ∀ i y, a[i]? = some y → y ≠ x := fun i y hy =>
      (hd 0 (i + 1) x y (by omega) (by simp) (by simpa using hy) hx).symm
    refine .inr ⟨x.toNat, hp, hdx' ▸ hmd, by simpa using hlen, ?_, ?_, ?_⟩
    · intro i e' y he hy
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      have := hg (i + 1) e' z (by simpa using he) (by simpa using hz)
      have hzx := hne i z hz
      unfold down
      by_cases hz1 : z = -1
      · subst hz1; rw [if_pos (show (-1 : Int) < x.toNat by omega)]; simpa using this
      · rw [if_neg hz1] at this
        obtain ⟨d', hz0, hdz, hmz⟩ := this
        by_cases hlt : z < x.toNat
        · rw [if_pos hlt, if_neg hz1]
          refine ⟨d', hz0, ?_, hmz⟩
          rw [List.getElem?_eraseIdx_of_lt (by omega)]; exact hdz
        · rw [if_neg hlt, if_neg (show ¬z - 1 = -1 by omega)]
          refine ⟨d', by omega, ?_, hmz⟩
          rw [List.getElem?_eraseIdx_of_ge (by omega), show (z - 1).toNat + 1 = z.toNat by omega]; exact hdz
    · intro i j y z hij hy hz hy1
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hy hz
      obtain ⟨y', hy', rfl⟩ := hy
      obtain ⟨z', hz', rfl⟩ := hz
      have hy1' : y' ≠ -1 := by intro h; subst h; unfold down at hy1; split at hy1 <;> omega
      have := hd (i + 1) (j + 1) y' z' (by omega) (by simpa using hy') (by simpa using hz') hy1'
      have := hne i y' hy'
      have := hne j z' hz'
      unfold down; split <;> split <;> omega
    · intro m hm
      have hm' : (if m < x.toNat then m else m + 1) < ds.length := by split <;> omega
      obtain ⟨i, hi⟩ := ho _ hm'
      cases i with
      | zero => simp at hi; split at hi <;> omega
      | succ i =>
        refine ⟨i, ?_⟩
        simp only [List.getElem?_cons_succ] at hi
        simp only [List.getElem?_map, hi, Option.map_some]
        unfold down; split <;> split <;> simp_all <;> omega

theorem assignable_cons (e : Expectation) (es : List Expectation) (ds : List Diagnostic) :
    assignable fe (e :: es) ds = true ↔
      (∃ p, ∃ hp : p < ds.length, meets fe e ds[p] = true ∧ assignable fe es (ds.eraseIdx p) = true) ∨
        (mayLack fe e = true ∧ assignable fe es ds = true) := by
  simp only [assignable, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true]
  constructor
  · rintro (⟨p, hp, hm, ha⟩ | h)
    · exact .inl ⟨p, hp, by rwa [getElem!_pos ds p hp] at hm, ha⟩
    · exact .inr h
  · rintro (⟨p, hp, hm, ha⟩ | h)
    · exact .inl ⟨p, hp, by rwa [getElem!_pos ds p hp], ha⟩
    · exact .inr h

/-- The search of `assignable` finds a way to give the expectations
messages exactly when there is one. -/
theorem assignable_iff (es : List Expectation) (ds : List Diagnostic) :
    assignable fe es ds = true ↔ ∃ a, Assigns fe es ds a := by
  induction es generalizing ds with
  | nil =>
    simp only [assignable, List.isEmpty_iff, assigns_nil]
    exact ⟨fun h => ⟨[], rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  | cons e es ih =>
    rw [assignable_cons]
    constructor
    · rintro (⟨p, hp, hm, ha⟩ | ⟨hl, ha⟩)
      · obtain ⟨a, ha⟩ := (ih _).mp ha
        exact ⟨_, assigns_take fe e es ds a p hp hm ha⟩
      · obtain ⟨a, ha⟩ := (ih _).mp ha
        exact ⟨_, assigns_skip fe e es ds a hl ha⟩
    · rintro ⟨a, ha⟩
      cases a with
      | nil => exact absurd ha.1 (by simp)
      | cons x a =>
        rcases assigns_cons fe e es ds x a ha with ⟨hl, ha⟩ | ⟨p, hp, hm, ha⟩
        · exact .inr ⟨hl, (ih _).mpr ⟨a, ha⟩⟩
        · exact .inl ⟨p, hp, hm, (ih _).mpr ⟨_, ha⟩⟩

/-- A message as `testing::ui_file` has it. -/
def toMessage (d : Diagnostic) : testing.Message := { line := d.line, severity := d.severity, text := d.text }

/-- An expectation as `testing::ui_file` has it. -/
def toExpectation (e : Expectation) : testing.Expectation :=
  { line := e.line, severity := e.severity, text := e.text, front_end := e.frontEnd?, optional? := e.optional }

/-- `decide`, whatever the instance, which may be classical. -/
theorem dec_true {p : Prop} {inst : Decidable p} : @decide p inst = true ↔ p := @decide_eq_true_iff p inst

theorem nth_ofList_nat {γ : Type} [Inhabited γ] (l : List γ) (i : Nat) (h : i < l.length) :
    (Fren.Seq.ofList l).nth (i : Int) = l[i] := by
  rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using h)]; simp

theorem forall_int (n : Nat) (P : Int → Prop) : (∀ i : Int, 0 ≤ i ∧ i < (n : Int) → P i) ↔ ∀ i : Nat, i < n → P i := by
  constructor
  · intro h i hi; exact h i ⟨by omega, by omega⟩
  · intro h i ⟨h0, hi⟩
    have := h i.toNat (by omega)
    rwa [show ((i.toNat : Nat) : Int) = i by omega] at this

theorem applies_iff (e : Expectation) : testing.applies? (toExpectation e) fe = e.applies fe := by
  rcases e with ⟨line, sev, text, _ | f, opt, at_⟩
  · simp [testing.applies?, toExpectation, Expectation.applies]
  · rw [Bool.eq_iff_iff]
    simp [testing.applies?, toExpectation, Expectation.applies, Fren.Prelude.Option.some.x0]

theorem mayLack_iff (e : Expectation) :
    ((toExpectation e).optional? = true ∨ ¬testing.applies? (toExpectation e) fe = true) ↔ mayLack fe e = true := by
  rw [applies_iff]; simp [mayLack, toExpectation]

theorem meets_iff (e : Expectation) (d : Diagnostic) :
    (testing.applies? (toExpectation e) fe = true ∧ testing.meets? (toMessage d) (toExpectation e) = true) ↔
      meets fe e d = true := by
  rw [applies_iff]
  simp only [meets, testing.meets?, toMessage, toExpectation, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩; exact ⟨⟨⟨h1, by omega⟩, h3⟩, h4⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h1, ⟨by omega, h3⟩, h4⟩

/-- `testing::assigns?` is `Assigns`. -/
theorem assigns_iff (es : List Expectation) (ds : List Diagnostic) (a : List Int) :
    testing.assigns? (Fren.Seq.ofList (ds.map toMessage)) (Fren.Seq.ofList (es.map toExpectation)) fe
      (Fren.Seq.ofList a) = true ↔ Assigns fe es ds a := by
  unfold testing.assigns?
  rw [dec_true]
  simp only [Fren.Seq.len_eq, Fren.Seq.toList_ofList, List.length_map]
  constructor
  · rintro ⟨⟨⟨hlen, hg⟩, hd⟩, ho⟩
    have hlen : a.length = es.length := by omega
    refine ⟨hlen, ?_, ?_, ?_⟩
    · intro i e x he hx
      have hi : i < es.length := (List.getElem?_eq_some_iff.mp he).1
      have he' : es[i] = e := (List.getElem?_eq_some_iff.mp he).2
      have hx' : a[i]'(by omega) = x := (List.getElem?_eq_some_iff.mp hx).2
      have := hg i ⟨by omega, by omega⟩
      unfold testing.gives? at this
      rw [dec_true] at this
      rw [nth_ofList_nat a i (by omega), nth_ofList_nat _ i (by simpa using hi), List.getElem_map, he', hx'] at this
      split at this
      · rename_i h1; rw [if_pos h1]; exact (mayLack_iff fe e).mp this
      · rename_i h1
        rw [if_neg h1]
        obtain ⟨⟨⟨h0, hl⟩, hap⟩, hm⟩ := this
        simp only [Fren.Seq.len_eq, Fren.Seq.toList_ofList, List.length_map] at hl
        refine ⟨ds[x.toNat]'(by omega), h0, by simp, (meets_iff fe e _).mp ⟨hap, ?_⟩⟩
        rw [Fren.Seq.nth_of_lt _ _ h0 (by simpa using hl)] at hm
        simpa only [Fren.Seq.toList_ofList, List.getElem_map] using hm
    · intro i j x y hij hx hy hx1
      have hi : i < a.length := (List.getElem?_eq_some_iff.mp hx).1
      have hj : j < a.length := (List.getElem?_eq_some_iff.mp hy).1
      have e1 : (Fren.Seq.ofList a).nth (i : Int) = x := by
        rw [nth_ofList_nat a i hi]; exact (List.getElem?_eq_some_iff.mp hx).2
      have e2 : (Fren.Seq.ofList a).nth (j : Int) = y := by
        rw [nth_ofList_nat a j hj]; exact (List.getElem?_eq_some_iff.mp hy).2
      have := hd i j ⟨⟨⟨by omega, by omega⟩, by omega⟩, by rw [e1]; exact hx1⟩
      rwa [e1, e2] at this
    · intro m hm
      obtain ⟨i, ⟨h0, hi⟩, hai⟩ := ho m ⟨by omega, by omega⟩
      refine ⟨i.toNat, ?_⟩
      rw [List.getElem?_eq_some_iff]
      refine ⟨by omega, ?_⟩
      rw [Fren.Seq.nth_of_lt _ _ h0 (by simp; omega)] at hai
      simpa using hai
  · rintro ⟨hlen, hg, hd, ho⟩
    refine ⟨⟨⟨by omega, ?_⟩, ?_⟩, ?_⟩
    · intro i ⟨h0, hi⟩
      have hi' : i.toNat < es.length := by omega
      have e1 : i = ((i.toNat : Nat) : Int) := by omega
      rw [e1]
      have := hg i.toNat es[i.toNat] (a[i.toNat]'(by omega)) (List.getElem?_eq_getElem hi')
        (List.getElem?_eq_getElem (by omega))
      unfold testing.gives?
      rw [dec_true]
      rw [nth_ofList_nat a i.toNat (by omega), nth_ofList_nat _ i.toNat (by simpa using hi'), List.getElem_map]
      split
      · rename_i h1; rw [if_pos h1] at this; exact (mayLack_iff fe _).mpr this
      · rename_i h1
        rw [if_neg h1] at this
        obtain ⟨d, h0, hd', hm⟩ := this
        have hl : (a[i.toNat]'(by omega)).toNat < ds.length := (List.getElem?_eq_some_iff.mp hd').1
        have hdd : ds[(a[i.toNat]'(by omega)).toNat] = d := (List.getElem?_eq_some_iff.mp hd').2
        obtain ⟨hap, hmm⟩ := (meets_iff fe _ _).mpr hm
        refine ⟨⟨⟨h0, by simp; omega⟩, hap⟩, ?_⟩
        rw [Fren.Seq.nth_of_lt _ _ h0 (by simp; omega)]
        simp only [Fren.Seq.toList_ofList, List.getElem_map, hdd]; exact hmm
    · intro i j ⟨⟨⟨h0, hij⟩, hj⟩, hx1⟩
      have hi' : i.toNat < a.length := by omega
      have hj' : j.toNat < a.length := by omega
      rw [Fren.Seq.nth_of_lt _ _ h0 (by simp; omega)] at hx1 ⊢
      rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simp; omega)]
      exact hd i.toNat j.toNat _ _ (by omega) (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _) hx1
    · intro m ⟨h0, hm⟩
      obtain ⟨i, hi⟩ := ho m.toNat (by omega)
      have hia : i < a.length := (List.getElem?_eq_some_iff.mp hi).1
      refine ⟨i, ⟨by omega, by omega⟩, ?_⟩
      rw [nth_ofList_nat a i hia, (List.getElem?_eq_some_iff.mp hi).2]
      omega

/-- `testing::met?` is what `assignable` decides. -/
theorem met_iff (es : List Expectation) (ds : List Diagnostic) :
    testing.met? (Fren.Seq.ofList (ds.map toMessage)) (Fren.Seq.ofList (es.map toExpectation)) fe = true ↔
      assignable fe es ds = true := by
  rw [assignable_iff]
  unfold testing.met?
  rw [dec_true]
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a.toList, (assigns_iff fe es ds a.toList).mp ha⟩
  · rintro ⟨a, ha⟩; exact ⟨Fren.Seq.ofList a, (assigns_iff fe es ds a).mpr ha⟩

theorem isEmpty_append (a b : Array String) : (a ++ b).isEmpty = (a.isEmpty && b.isEmpty) := by
  rw [Bool.eq_iff_iff]; simp [Array.isEmpty_iff]

theorem messageFailures_isEmpty (es : Array Expectation) (ds : Array Diagnostic) :
    (messageFailures fe es ds).isEmpty = assignable fe es.toList ds.toList := by
  unfold messageFailures
  split
  · simp_all
  · rename_i h
    simp only [Bool.not_eq_true] at h
    rw [h]
    dsimp only
    split <;> simp_all

-- `check` reports nothing exactly when the messages meet the expectations,
-- by `assignable`, and the summary and exit code are those expected.
impl ui_check: testing::ui_file for (ds : List Diagnostic) (es : List Expectation) (fe : String)
    (s gs : Option String) (x gx : Option Nat) {
  ms := Fren.Seq.ofList (ds.map toMessage),
  es := Fren.Seq.ofList (es.map toExpectation),
  front_end := fe,
  summary := s,
  got_summary := gs,
  exit := x.map (fun n : Nat => (n : Int)),
  got_exit := gx.map (fun n : Nat => (n : Int)),
  passes? := (check fe { expectations := es.toArray, summary? := s, exit? := x } ds.toArray gs gx).isEmpty,
} by
  intro ds es fe s gs x gx _
  show _ ↔ _
  rw [met_iff]
  simp only [check, isEmpty_append, Bool.and_eq_true, messageFailures_isEmpty, and_assoc]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · cases s <;> cases gs <;> simp [summaryFailures, Fren.Prelude.Option.some.x0]
  · cases x <;> cases gx <;> simp [exitFailures, Fren.Prelude.Option.some.x0] <;> omega

end Matching

trusted testing::fresh: "Lake rebuilds a module when a file that its library needs changed since its last build, which is Lake's rule and not checked by Fren; that the modules that read files read only files that their library needs is checked by `lake test`'s `libraries` job, which reads the sources and `lakefile.lean`"

end Fren.Impls.Testing
