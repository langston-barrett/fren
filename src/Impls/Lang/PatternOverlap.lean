-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-! ## The overlap of patterns -/

section PatternOverlap
open Fren.Core

/-- The integers of an interval, as `lang::in_range?` reads a range. -/
def inIv (iv : Option Int × Option Int) (n : Int) : Prop := (∀ l, iv.1 = some l → l ≤ n) ∧ (∀ h, iv.2 = some h → n ≤ h)

/-- The integer of an interval that `Wit.ofInterval` picks. -/
def ivPoint : Option Int × Option Int → Int
  | (some l, _) => l
  | (none, some h) => h
  | (none, none) => 0

theorem meet_some (ty : Fren.Core.PatTy) (a b iv : Option Int × Option Int)
    (h : Fren.Core.meetIntervals ty a b = some iv) :
    inIv a (ivPoint iv) ∧ inIv b (ivPoint iv) ∧ (ty = .nat → 0 ≤ ivPoint iv) := by
  rcases a with ⟨_ | a1, _ | a2⟩ <;> rcases b with ⟨_ | b1, _ | b2⟩ <;>
    by_cases hn : ty = .nat <;>
    simp [Fren.Core.meetIntervals, Fren.Core.maxBound, Fren.Core.minBound, hn] at h <;>
    (try obtain ⟨hc, rfl⟩ := h) <;> (try subst h) <;>
    simp [inIv, ivPoint, hn] <;> omega

theorem meet_none (ty : Fren.Core.PatTy) (a b : Option Int × Option Int)
    (h : Fren.Core.meetIntervals ty a b = none) (n : Int) (ha : inIv a n) (hb : inIv b n) (hn : ty = .nat → 0 ≤ n) :
    False := by
  rcases a with ⟨_ | a1, _ | a2⟩ <;> rcases b with ⟨_ | b1, _ | b2⟩ <;>
    by_cases hN : ty = .nat <;>
    simp [Fren.Core.meetIntervals, Fren.Core.maxBound, Fren.Core.minBound, hN] at h <;>
    simp [inIv] at ha hb <;> simp [hN] at hn <;> omega

/-- An enumeration of `k + 1` variants, each with one payload value of `pty`. -/
def ovSigs (k : Nat) (pty : PatTy) : Sigs := fun _ => (Array.range (k + 1)).map fun i => (Lean.Name.mkNum .anonymous i, #[pty])

theorem ow_ii (sigs : Sigs) (ty : PatTy) (a b c d : Option Int) :
    Pat.overlapWit? sigs ty (.int a b) (.int c d) = (meetIntervals ty (a, b) (c, d)).map Wit.ofInterval := by
  rw [Pat.overlapWit?]
  simp only [overlapStep, Pat.headKind, Pat.sameHead]
  cases meetIntervals ty (a, b) (c, d) <;> simp
  all_goals (intros; simp_all)

theorem sw_i (sigs : Sigs) (ty : PatTy) (c d : Option Int) :
    Pat.someWit? sigs ty (.int c d) = (meetIntervals ty (c, d) (none, none)).map Wit.ofInterval := by
  rw [Pat.someWit?]

theorem ow_wi (sigs : Sigs) (ty : PatTy) (c d : Option Int) :
    Pat.overlapWit? sigs ty (.wild false) (.int c d) = (meetIntervals ty (c, d) (none, none)).map Wit.ofInterval := by
  rw [Pat.overlapWit?]
  simp [overlapStep, Pat.headKind, sw_i]
  all_goals (intros; simp_all)

theorem ow_iw (sigs : Sigs) (ty : PatTy) (c d : Option Int) :
    Pat.overlapWit? sigs ty (.int c d) (.wild false) = (meetIntervals ty (c, d) (none, none)).map Wit.ofInterval := by
  rw [Pat.overlapWit?]
  simp [overlapStep, Pat.headKind, sw_i]
  all_goals (intros; simp_all)

theorem ow_ww (sigs : Sigs) (ty : PatTy) : Pat.overlapWit? sigs ty (.wild false) (.wild false) = some .any := by
  rw [Pat.overlapWit?]
  simp [overlapStep, Pat.headKind, Pat.someWit?]
  all_goals (intros; simp_all)

theorem sw_c (k : Nat) (pty : PatTy) (i : Nat) (hi : i ≤ k) (c d : Option Int) :
    Pat.someWit? (ovSigs k pty) (.enum `E []) (.ctor i #[.int c d]) =
      (meetIntervals pty (c, d) (none, none)).map fun iv => .ctor (.num `E i) #[Wit.ofInterval iv] := by
  rw [Pat.someWit?]
  simp [ctorTys, ovSigs, sw_i, Ctor.wit, Nat.lt_succ_of_le hi]
  cases meetIntervals pty (c, d) (none, none) <;> simp
  rfl

theorem ow_wv (k : Nat) (pty : PatTy) (i : Nat) (hi : i ≤ k) (c d : Option Int) :
    Pat.overlapWit? (ovSigs k pty) (.enum `E []) (.wild false) (.ctor i #[.int c d]) =
      (meetIntervals pty (c, d) (none, none)).map fun iv => .ctor (.num `E i) #[Wit.ofInterval iv] := by
  rw [Pat.overlapWit?]
  simp [overlapStep, Pat.headKind, sw_c k pty i hi]
  all_goals (intros; simp_all)

theorem ow_vw (k : Nat) (pty : PatTy) (i : Nat) (hi : i ≤ k) (c d : Option Int) :
    Pat.overlapWit? (ovSigs k pty) (.enum `E []) (.ctor i #[.int c d]) (.wild false) =
      (meetIntervals pty (c, d) (none, none)).map fun iv => .ctor (.num `E i) #[Wit.ofInterval iv] := by
  rw [Pat.overlapWit?]
  simp [overlapStep, Pat.headKind, sw_c k pty i hi]
  all_goals (intros; simp_all)

theorem ow_vv (k : Nat) (pty : PatTy) (i j : Nat) (hi : i ≤ k) (a b c d : Option Int) :
    Pat.overlapWit? (ovSigs k pty) (.enum `E []) (.ctor i #[.int a b]) (.ctor j #[.int c d]) =
      if i = j then (meetIntervals pty (a, b) (c, d)).map fun iv => .ctor (.num `E i) #[Wit.ofInterval iv]
      else none := by
  rw [Pat.overlapWit?]
  simp only [overlapStep, Pat.headKind, Pat.sameHead]
  by_cases hij : i = j
  · subst hij
    simp [ctorTys, ovSigs, ow_ii, Ctor.wit, Nat.lt_succ_of_le hi]
    cases meetIntervals pty (a, b) (c, d) <;> simp
    rfl
  · simp [hij]
  all_goals (intros; simp_all)

/-- The bounds of a range, each where it has one. -/
def toBounds (r : lang.IntRange) : Option Int × Option Int :=
  (if r.bounded_below? then some r.low else none, if r.bounded_above? then some r.high else none)

def toPat (p : lang.SimplePattern) : Pat :=
  match p.shape with
  | .Wildcard => .wild false
  | .Integers => .int (toBounds p.range).1 (toBounds p.range).2
  | .Variant => .ctor p.variant.toNat #[.int (toBounds p.payload).1 (toBounds p.payload).2]

/-- The integer of a witness, `0` for any. -/
def numOf : Wit → Int
  | .int (some n) _ => n
  | _ => 0

/-- The variant, by its position, that a witness's path names. -/
def variantOf : Lean.Name → Int
  | .num _ k => k
  | _ => 0

/-- A witness as a value of `lang::pattern_overlap`, `0` for any integer. -/
def toValue : Option Wit → lang.SimpleValue
  | some (.int (some n) _) => ⟨0, n⟩
  | some (.ctor p args) => ⟨variantOf p, ((args[0]?).map numOf).getD 0⟩
  | _ => ⟨0, 0⟩

/-- The type of the integers: `Nat` or `Int`. -/
def ptyOf (nat : Bool) : PatTy := if nat then .nat else .int

/-- What `Pat.overlapWit?` gives two patterns of `lang::pattern_overlap`. -/
def owOf (f s : lang.SimplePattern) (nat : Bool) : Option Wit :=
  Pat.overlapWit? (ovSigs (max f.variant.toNat s.variant.toNat) (ptyOf nat))
    (if f.shape = .Variant ∨ s.shape = .Variant then .enum `E [] else ptyOf nat) (toPat f) (toPat s)

theorem ofInterval_eq (iv : Option Int × Option Int) :
    Wit.ofInterval iv = .int (some (ivPoint iv)) (some (ivPoint iv)) := by
  rcases iv with ⟨_ | _, _ | _⟩ <;> rfl

theorem inIv_bounds (r : lang.IntRange) (n : Int) :
    inIv (toBounds r) n ↔ ((r.bounded_below? = false ∨ r.low ≤ n) ∧ (r.bounded_above? = false ∨ n ≤ r.high)) := by
  rcases r with ⟨_ | _, l, _ | _, h⟩ <;> simp [inIv, toBounds]

theorem natOk (nat : Bool) (n : Int) : (ptyOf nat = .nat → 0 ≤ n) ↔ (nat = false ∨ 0 ≤ n) := by
  cases nat <;> simp [ptyOf]

theorem inIv_none (n : Int) : inIv (none, none) n := by simp [inIv]

-- Both front ends decide whether two arms' patterns overlap, and name the
-- value that both match, by `Pat.overlapWit?`: here of the patterns of
-- one value, `_`, ranges and variants with one value of a payload, as the
-- front ends resolve them (`toPat`), and its witness read back (`toValue`).
impl pattern_overlap: lang::pattern_overlap for (first second : lang.SimplePattern) (nat : Bool) (v : lang.SimpleValue) {
  first := first,
  second := second,
  nat? := nat,
  v := v,
  overlap? := (owOf first second nat).isSome,
  witness := toValue (owOf first second nat),
} by
  intro first second nat v hA
  rcases first with ⟨fs, fr, fv, fp⟩
  rcases second with ⟨ss, sr, sv, sp⟩
  simp [lang.pattern_overlap.assumes, lang.pattern_overlap.assume.typed, lang.pattern_overlap.assume.variants] at hA
  obtain ⟨hfv, hsv⟩ := hA
  simp only [lang.pattern_overlap.ensures, lang.pattern_overlap.ensure.common, lang.pattern_overlap.ensure.complete]
  cases fs <;> cases ss <;> simp at hfv <;> simp [owOf, toPat]
  · simp [ow_ww, toValue]
  · rw [ow_wi]
    cases hm : meetIntervals (ptyOf nat) ((toBounds sr).fst, (toBounds sr).snd) (none, none) with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_implies, true_and]
      intro h1 h2 h3
      exact (meet_none _ _ _ hm v.number ((inIv_bounds sr _).2 ⟨h1, h2⟩) (inIv_none _) ((natOk nat _).2 h3)).elim
    | some iv =>
      obtain ⟨h1, -, h3⟩ := meet_some _ _ _ _ hm
      simp [toValue, ofInterval_eq]
      rw [inIv_bounds] at h1; rw [natOk] at h3; simp_all
  · -- `_` and a variant.
    rw [ow_wv _ _ _ (Nat.le_max_right _ _)]
    cases hm : meetIntervals (ptyOf nat) ((toBounds sp).fst, (toBounds sp).snd) (none, none) with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_implies, true_and]
      intro _ h1 h2 h3
      exact (meet_none _ _ _ hm v.number ((inIv_bounds sp _).2 ⟨h1, h2⟩) (inIv_none _) ((natOk nat _).2 h3)).elim
    | some iv =>
      obtain ⟨h1, -, h3⟩ := meet_some _ _ _ _ hm
      simp [toValue, ofInterval_eq, variantOf, numOf, Int.toNat_of_nonneg hsv.2]
      rw [inIv_bounds] at h1; rw [natOk] at h3; simp_all
  · -- A range and `_`.
    rw [ow_iw]
    cases hm : meetIntervals (ptyOf nat) ((toBounds fr).fst, (toBounds fr).snd) (none, none) with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_implies, true_and]
      intro h1 h2 h3
      exact (meet_none _ _ _ hm v.number ((inIv_bounds fr _).2 ⟨h1, h2⟩) (inIv_none _) ((natOk nat _).2 h3)).elim
    | some iv =>
      obtain ⟨h1, -, h3⟩ := meet_some _ _ _ _ hm
      simp [toValue, ofInterval_eq]
      rw [inIv_bounds] at h1; rw [natOk] at h3; simp_all
  · -- Two ranges.
    rw [ow_ii]
    cases hm : meetIntervals (ptyOf nat) ((toBounds fr).fst, (toBounds fr).snd) ((toBounds sr).fst, (toBounds sr).snd) with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_implies, true_and]
      intro h1 h2 h1' h2' h3
      exact (meet_none _ _ _ hm v.number ((inIv_bounds fr _).2 ⟨h1, h2⟩) ((inIv_bounds sr _).2 ⟨h1', h2'⟩)
        ((natOk nat _).2 h3)).elim
    | some iv =>
      obtain ⟨h1, h2, h3⟩ := meet_some _ _ _ _ hm
      simp [toValue, ofInterval_eq]
      rw [inIv_bounds] at h1 h2; rw [natOk] at h3; simp_all
  · -- A variant and `_`.
    rw [ow_vw _ _ _ (Nat.le_max_left _ _)]
    cases hm : meetIntervals (ptyOf nat) ((toBounds fp).fst, (toBounds fp).snd) (none, none) with
    | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_implies, true_and]
      intro _ h1 h2 h3
      exact (meet_none _ _ _ hm v.number ((inIv_bounds fp _).2 ⟨h1, h2⟩) (inIv_none _) ((natOk nat _).2 h3)).elim
    | some iv =>
      obtain ⟨h1, -, h3⟩ := meet_some _ _ _ _ hm
      simp [toValue, ofInterval_eq, variantOf, numOf, Int.toNat_of_nonneg hsv.1]
      rw [inIv_bounds] at h1; rw [natOk] at h3; simp_all
  · -- Two variants.
    rw [ow_vv _ _ _ _ (Nat.le_max_left _ _)]
    by_cases hij : fv.toNat = sv.toNat
    · have hfs : fv = sv := by omega
      subst hfs
      simp only [↓reduceIte]
      cases hm : meetIntervals (ptyOf nat) ((toBounds fp).fst, (toBounds fp).snd) ((toBounds sp).fst, (toBounds sp).snd) with
      | none =>
        simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_implies, true_and]
        intro _ h1 h2 _ h1' h2' h3
        exact (meet_none _ _ _ hm v.number ((inIv_bounds fp _).2 ⟨h1, h2⟩) ((inIv_bounds sp _).2 ⟨h1', h2'⟩)
          ((natOk nat _).2 h3)).elim
      | some iv =>
        obtain ⟨h1, h2, h3⟩ := meet_some _ _ _ _ hm
        simp [toValue, ofInterval_eq, variantOf, numOf, Int.toNat_of_nonneg hsv.1]
        rw [inIv_bounds] at h1 h2; rw [natOk] at h3; simp_all
    · simp only [if_neg hij, Option.isSome_none, Bool.false_eq_true, false_implies, true_and]
      intro h1 _ _ h2
      omega
end PatternOverlap

end Fren.Impls
