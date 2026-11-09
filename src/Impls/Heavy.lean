-- keep-sorted start
import Fren.Impl
import Heavy.Forecast
import Reqs.Testing
-- keep-sorted end
open Fren.Lang

/-! The Std-only forecast kernel, bound to `testing::heavy_memory_prediction`.
Log decoding and OS operations remain tested claims in `Impls.Trace`. -/

namespace Fren.Impls.Heavy

open Heavy.Forecast

impl prediction_key: testing::heavy_prediction_key
    for (command : Option String) (kind : String) {
  command := command,
  kind := kind,
  uses_command? := (predictionKey command kind).1,
  key := (predictionKey command kind).2,
} by
  intro command kind _
  cases command <;> simp [fren_spec, predictionKey]

def observation (o : Observation String) : testing.MemoryObservation :=
  ⟨o.event, o.key, o.ended, o.peak⟩

def history : List (Observation String) → testing.MemoryHistory
  | [] => .Nil
  | o :: rest => .Cons (observation o) (history rest)

def peaks : Peaks → testing.MemoryPeaks
  | [] => .Nil
  | (t, p) :: rest => .Cons t p (peaks rest)

theorem eligible_eq (o : Observation String) (key : String) (cutoff now : Int) :
    testing.memory_eligible? (observation o) key cutoff now = eligible o key cutoff now := by
  cases o with
  | mk event key' ended peak =>
    cases ended <;> cases peak <;>
      simp [testing.memory_eligible?, observation, eligible, Prelude.Option.some.x0,
        Fren.Str.lit, Bool.and_assoc]

theorem take_eq (ps : Peaks) (n : Nat) :
    testing.memory_take (n : Int) (peaks ps) = peaks (take n ps) := by
  induction ps generalizing n with
  | nil => simp [testing.memory_take, peaks, take]
  | cons x rest ih =>
    obtain ⟨t, p⟩ := x
    by_cases hn : n = 0
    · subst n; simp [peaks, testing.memory_take, take]
    · have hc : (n : Int) - 1 = ((n - 1 : Nat) : Int) := by omega
      simp [peaks, testing.memory_take, take, hn, hc, ih]

theorem insert_eq (ps : Peaks) (t p : Int) (n : Nat) :
    testing.memory_insert t p (n : Int) (peaks ps) = peaks (insert t p n ps) := by
  induction ps generalizing n with
  | nil => by_cases hn : n = 0 <;> simp [peaks, testing.memory_insert, Heavy.Forecast.insert, hn]
  | cons x rest ih =>
    obtain ⟨u, q⟩ := x
    by_cases hn : n = 0
    · subst n; simp [peaks, testing.memory_insert, Heavy.Forecast.insert]
    · have hc : (n : Int) - 1 = ((n - 1 : Nat) : Int) := by omega
      simp only [peaks, testing.memory_insert, Heavy.Forecast.insert, Int.natCast_eq_zero,
        hn, if_false, hc]
      split
      · rw [← peaks, take_eq]; rfl
      · simp [peaks, ih]

theorem recent_eq (hs : List (Observation String)) (key : String)
    (cutoff now : Int) (n : Nat) :
    testing.memory_recent (history hs) key cutoff now (n : Int) = peaks (recent hs key cutoff now n) := by
  induction hs with
  | nil => rfl
  | cons o rest ih =>
    obtain ⟨event, key', ended, peak⟩ := o
    have he := eligible_eq (Observation.mk event key' ended peak) key cutoff now
    simp only [observation] at he
    cases ended <;> cases peak <;>
      simp only [history, testing.memory_recent, observation, recent, ih]
    all_goals first | rfl | skip
    rw [he]
    split
    · exact insert_eq _ _ _ _
    · rfl

theorem maximum_eq (ps : Peaks) : testing.memory_max (peaks ps) = maximum ps := by
  induction ps with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨t, p⟩ := x
    simp only [peaks, testing.memory_max, maximum, ih]
    cases maximum rest with
    | none => rfl
    | some q => simp only [Int.max_def, Option.some.injEq]; split <;> split <;> omega

theorem count_eq (ps : Peaks) : testing.memory_count (peaks ps) = ps.length := by
  induction ps with
  | nil => rfl
  | cons x rest ih => obtain ⟨t, p⟩ := x; simp [peaks, testing.memory_count, ih, Nat.add_comm]

/-- The maximum covers every selected observation, not just the head
covered by the recursive function's one-step contract. -/
theorem maximum_covers (ps : Peaks) (t p : Int) (h : (t, p) ∈ ps) :
    ∃ m, maximum ps = some m ∧ p ≤ m := by
  induction ps with
  | nil => simp at h
  | cons x rest ih =>
    obtain ⟨u, q⟩ := x
    rcases List.mem_cons.mp h with he | hr
    · cases he
      cases hm : maximum rest with
      | none => exact ⟨p, by simp [maximum, hm]⟩
      | some m =>
        refine ⟨max p m, by simp [maximum, hm], ?_⟩
        simp only [Int.max_def]; split <;> omega
    · obtain ⟨m, hm, hp⟩ := ih hr
      refine ⟨max q m, by simp [maximum, hm], ?_⟩
      simp only [Int.max_def]; split <;> omega

impl memory_prediction: testing::heavy_memory_prediction
    for (hs : List (Observation String))
      (key : String) (cutoff now : Int) (n : Nat) {
  history := history hs,
  key := key,
  cutoff := cutoff,
  now := now,
  n := n,
  prediction := (predict hs key cutoff now n).1,
  jobs := (predict hs key cutoff now n).2,
} by
  intro hs key cutoff now n _
  simp [fren_spec, predict, recent_eq, maximum_eq, count_eq]

end Fren.Impls.Heavy
