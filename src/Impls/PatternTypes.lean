-- keep-sorted start
import Fren.Impl
import FrenCore.PatternTypes
import Reqs.Impl
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # Pattern types (`Reqs/Lang/Types#subset-types`, `Reqs/Impl#interpretations`)

The rules of pattern types, proved of the functions that both front ends
and the evaluator call: membership in an integer pattern, the count of
its integers, the obligation of a value, and an interpretation's
obligation. -/

namespace Fren.Impls.PatternTypes

/-- A bound, as the Reqs write it. -/
def toBound : Option Int → lang.Bound
  | none => .Open
  | some v => .At v

/-- A range, as the Reqs write an alternative. -/
def toAlt (iv : Option Int × Option Int) : lang.Alternative := ⟨toBound iv.1, toBound iv.2⟩

theorem above_toBound (b : Option Int) (x : Int) : lang.above? (toBound b) x = b.all (· ≤ x) := by
  cases b <;> simp [toBound, lang.above?, lang.Bound.At.x0]

theorem below_toBound (b : Option Int) (x : Int) : lang.below? (toBound b) x = b.all (x ≤ ·) := by
  cases b <;> simp [toBound, lang.below?, lang.Bound.At.x0]

theorem lo_iff (iv : Option Int × Option Int) (x : Int) :
    ((toAlt iv).lo = .Open ∨ lang.Bound.At.x0 (toAlt iv).lo ≤ x) ↔ iv.1.all (· ≤ x) := by
  obtain ⟨a, b⟩ := iv; cases a <;> simp [toAlt, toBound, lang.Bound.At.x0]

theorem hi_iff (iv : Option Int × Option Int) (x : Int) :
    ((toAlt iv).hi = .Open ∨ x ≤ lang.Bound.At.x0 (toAlt iv).hi) ↔ iv.2.all (x ≤ ·) := by
  obtain ⟨a, b⟩ := iv; cases b <;> simp [toAlt, toBound, lang.Bound.At.x0]

theorem nth_alts (ivs : List (Option Int × Option Int)) (i : Nat) (h : i < ivs.length) :
    (Fren.Seq.ofList (ivs.map toAlt)).nth i = toAlt ivs[i] := by
  rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using h)]
  simp

/-- The first range that `x` is in is one, and it is in it. -/
theorem index_holds (ivs : List (Option Int × Option Int)) (x : Int) (h : Fren.Core.intervalsHold ivs x = true) :
    ∃ i, ∃ hi : i < ivs.length, Fren.Core.intervalIndex? ivs x = some i ∧
      Fren.Core.intervalHolds ivs[i].1 ivs[i].2 x = true := by
  induction ivs with
  | nil => simp [Fren.Core.intervalsHold] at h
  | cons iv rest ih =>
    obtain ⟨lo, hi⟩ := iv
    by_cases hh : Fren.Core.intervalHolds lo hi x = true
    · exact ⟨0, by simp, by simp [Fren.Core.intervalIndex?, hh], by simpa using hh⟩
    · have hr : Fren.Core.intervalsHold rest x = true := by
        simp only [Fren.Core.intervalsHold, List.any_cons, Bool.or_eq_true] at h
        rcases h with h | h
        · exact absurd h hh
        · exact h
      obtain ⟨i, hi, hidx, hhold⟩ := ih hr
      exact ⟨i + 1, by simp; omega, by simp [Fren.Core.intervalIndex?, hh, hidx], by simpa using hhold⟩

-- Membership, by the function that matches an integer pattern for the
-- checks' constraints and obligations and for the evaluator
-- (`Fren.Core.Pat.matchesVal`, `FrenCli.Eval.patHolds`).
impl pattern_member: lang::pattern_member for (ivs : List (Option Int × Option Int)) (x k : Int) {
  alts := Fren.Seq.ofList (ivs.map toAlt),
  x := x,
  k := k,
  member? := Fren.Core.intervalsHold ivs x,
  witness := ((Fren.Core.intervalIndex? ivs x).getD 0 : Nat),
} by
  intro ivs x k
  simp [fren_spec]
  refine ⟨fun h0 hk hlo hhi => ?_, fun hm => ?_⟩
  · have hk' : k.toNat < ivs.length := by omega
    have hkk : k = ((k.toNat : Nat) : Int) := by omega
    rw [hkk, nth_alts ivs k.toNat hk'] at hlo hhi
    simp only [Fren.Core.intervalsHold, List.any_eq_true]
    refine ⟨ivs[k.toNat], List.getElem_mem _, ?_⟩
    simp [Fren.Core.intervalHolds, (lo_iff _ x).1 hlo, (hi_iff _ x).1 hhi]
  · obtain ⟨i, hi, hidx, hhold⟩ := index_holds ivs x hm
    rw [hidx]
    simp only [Option.getD_some, nth_alts ivs i hi]
    simp only [Fren.Core.intervalHolds, Bool.and_eq_true] at hhold
    exact ⟨⟨hi, (lo_iff _ x).2 hhold.1⟩, (hi_iff _ x).2 hhold.2⟩

-- How many integers a pattern matches, counted from its bounds by the
-- function that both front ends call to range a quantifier over a pattern
-- type (`Fren.Core.Pat.intCount?`, `Fren.Core.PTy.count?`).
impl pattern_count: lang::pattern_count for (ivs : List (Option Int × Option Int)) {
  alts := Fren.Seq.ofList (ivs.map toAlt),
  finite? := Fren.Core.intervalsFinite ivs,
  count := (Fren.Core.intervalsCount? ivs).getD 0,
} by
  intro ivs
  rcases ivs with _ | ⟨⟨a1, a2⟩, _ | ⟨⟨b1, b2⟩, _ | ⟨c, rest⟩⟩⟩
  · simp [fren_spec, Fren.Seq.ext_iff, Fren.Core.intervalsFinite, Fren.Core.intervalsCount?, Fren.Core.mergeIntervals,
      Fren.Core.totalWidth]
  · cases a1 <;> cases a2 <;> simp [fren_spec, Fren.Seq.ext_iff, Fren.Seq.nth, toAlt, toBound, lang.width, lang.bounded?,
      lang.bound_value, Fren.Core.intervalsFinite, Fren.Core.intervalsCount?, Fren.Core.mergeIntervals,
      Fren.Core.mergeInterval, Fren.Core.addInterval, Fren.Core.totalWidth]
    rename_i l h
    by_cases c : l ≤ h <;> simp [c] <;> omega
  · match a1, a2, b1, b2 with
    | some l1, some h1, some l2, some h2 =>
      by_cases c1 : l1 ≤ h1 <;> by_cases c2 : l2 ≤ h2 <;> by_cases c3 : h2 + 1 < l1 <;> by_cases c4 : h1 + 1 < l2 <;>
        simp [fren_spec, Fren.Seq.ext_iff, Fren.Seq.nth, toAlt, toBound, lang.width, lang.bounded?, lang.bound_value,
          Fren.Core.intervalsFinite, Fren.Core.intervalsCount?, Fren.Core.mergeIntervals,
          Fren.Core.mergeInterval, Fren.Core.addInterval, Fren.Core.totalWidth, c1, c2, c3, c4] <;>
        omega
    | none, _, _, _ | some _, none, _, _ | some _, some _, none, _ | some _, some _, some _, none =>
      simp [fren_spec, Fren.Seq.ext_iff, Fren.Seq.nth, toAlt, toBound, lang.bounded?, Fren.Core.intervalsFinite,
        Fren.Core.intervalsCount?]
  · simp only [fren_spec]
    intro h
    exfalso
    simp at h
    omega

/-- Whether a range has both bounds, as `Fren.Core.intervalsFinite` asks of each. -/
def hasBounds (iv : Option Int × Option Int) : Bool := iv.1.isSome && iv.2.isSome

theorem intervalsFinite_iff (ivs : List (Option Int × Option Int)) :
    Fren.Core.intervalsFinite ivs = true ↔ ∀ iv ∈ ivs, hasBounds iv = true := by
  induction ivs with
  | nil => simp [Fren.Core.intervalsFinite]
  | cons iv rest ih =>
    obtain ⟨a, b⟩ := iv
    have : Fren.Core.intervalsFinite ((a, b) :: rest) = (hasBounds (a, b) && Fren.Core.intervalsFinite rest) := by
      cases a <;> cases b <;> simp [Fren.Core.intervalsFinite, hasBounds]
    rw [this]; simp [ih]

-- When a pattern's alternatives are counted, for any number of them: by
-- the functions that both front ends call (`Fren.Core.intervalsFinite`,
-- `Fren.Core.intervalsCount?`), whichever alternatives they are.
impl pattern_bounds: lang::pattern_bounds for (ivs : List (Option Int × Option Int)) {
  los := Fren.Seq.ofList (ivs.map (toBound ·.1)),
  his := Fren.Seq.ofList (ivs.map (toBound ·.2)),
  finite? := Fren.Core.intervalsFinite ivs,
  counted? := (Fren.Core.intervalsCount? ivs).isSome,
} by
  intro ivs
  simp only [fren_spec]
  simp
  refine ⟨?_, ?_⟩
  · rw [intervalsFinite_iff]
    constructor
    · intro h
      refine ⟨fun a b hm => ?_, fun a b hm => ?_⟩ <;> have := h _ hm <;> cases a <;> cases b <;>
        simp_all [hasBounds, toBound]
    · rintro ⟨h1, h2⟩ ⟨a, b⟩ hm
      have := h1 a b hm
      have := h2 a b hm
      cases a <;> cases b <;> simp_all [hasBounds, toBound]
  · simp only [Fren.Core.intervalsCount?]
    split <;> simp_all

/-- A sample type of the kind `k`, for `lang::obligation`. -/
def sampleTy : lang.ValueType → Fren.Core.Ty
  | .BoolTy => .bool
  | .IntTy => .int
  | .NatTy => .nat
  | .StringTy => .string
  | .EnumTy => .enum `e []
  | .RecordTy => .record `r []
  | .AbstractTy => .abstract `a
  | .SetTy => .set .int
  | .RelTy => .rel .int .int
  | .SeqTy => .seq .int

/-- An element type's obligation that asks `d`. -/
def sampleCons : lang.Duty → Option Fren.Core.Cons
  | .Nothing => none
  | .Matches => some (.pat .int (.wild))
  | .Each => some (.elems false .int (.pat .int (.wild)))
  | .MatchesAndEach => some (.all #[.elems false .int (.pat .int (.wild)), .pat .int (.wild)])

/-- What the obligation `o?` asks (`lang::Duty`). -/
def dutyOf : Option Fren.Core.Cons → lang.Duty
  | none => .Nothing
  | some (.pat ..) => .Matches
  | some (.elems ..) | some (.pairs ..) => .Each
  | some (.all _) => .MatchesAndEach
  | some _ => .Nothing

def toValuePlace : Fren.Core.ValuePlace → lang.ValuePlace
  | .definition => .Definition
  | .argument => .Argument
  | .field => .Field
  | .payload => .Payload
  | .construction => .Construction
  | .letDefinition => .Let
  | .body => .Body
  | .constant => .Constant
  | .binding => .Binding

-- The obligation that both front ends ask where a value is given
-- (`Fren.Core.siteObligation`, `Fren.Core.obligationCons`, which
-- `Fren.Core.PTy.obligation` applies to each element type).
impl obligation: lang::obligation for (pl : Fren.Core.ValuePlace) (k : lang.ValueType) (p : Bool) (e : lang.Duty) {
  place := toValuePlace pl,
  type_kind := k,
  restricted? := p,
  element := e,
  duty := dutyOf (Fren.Core.siteObligation pl
    (Fren.Core.obligationCons (sampleTy k) (if p then some (.wild) else none) (sampleCons e) none)),
} by
  intro pl k p e _
  cases pl <;> cases k <;> cases p <;> cases e <;>
    simp [fren_spec, toValuePlace, sampleTy, sampleCons, dutyOf, Fren.Core.siteObligation, Fren.Core.obligationCons,
      Fren.Core.Cons.allOf?]

end Fren.Impls.PatternTypes
