-- keep-sorted start
import Fren.Impl
import Fren.Literate
-- keep-sorted end

/-!
# Run-length encoding in Lean

An encoder over lists, built from one `step` function, which an `impl`
proves meets the spec's `rle::step`. The theorems then say what the spec
can't yet, about whole lists: decoding an encoding gives back the input,
adjacent runs hold different values, and every run has at least one value.
-/

open Fren.Lang

-- The spec, in its module `rle`.
#fren_md "rle.fren"

namespace Rle

open rle

/-- One step of the encoder: extend the current run, or start a new one and
emit the current. -/
def step (current : Option Run) (next : Int) : Run × Option Run :=
  match current with
  | some r =>
    if r.value = next then ({ value := next, count := r.count + 1 }, none)
    else ({ value := next, count := 1 }, some r)
  | none => ({ value := next, count := 1 }, none)

-- `step` is the spec's procedure, resolved from the spec's module, `rle`.
impl step_meets: step for (c : Option Run) (n : Int) {
  current := c, next := n, run := (Rle.step c n).1, emitted := (Rle.step c n).2
} by
  intro c n h
  cases c with
  | none => simp [fren_spec, Rle.step, Fren.Prelude.Option.some.x0]
  | some r =>
    simp [fren_spec, Fren.Prelude.Option.some.x0] at h
    by_cases hv : r.value = n <;> simp [fren_spec, Rle.step, Fren.Prelude.Option.some.x0, hv, h] <;> omega

/-- Encodes `xs` after the run `current`, by `step`, and emits the last run at
the end. -/
def encodeFrom (current : Option Run) : List Int → List Run
  | [] => current.toList
  | x :: xs => (step current x).2.toList ++ encodeFrom (some (step current x).1) xs

/-- The run-length encoding of `xs`. -/
def encode (xs : List Int) : List Run := encodeFrom none xs

/-- The values that `runs` encode. -/
def decode (runs : List Run) : List Int := runs.flatMap fun r => List.replicate r.count r.value

/-- `decode` distributes over `++`. -/
theorem decode_append (a b : List Run) : decode (a ++ b) = decode a ++ decode b := by
  simp [decode]

/-- Encoding after `current` decodes to `current`'s values, then the input. -/
theorem decode_encodeFrom (current : Option Run) (xs : List Int) :
    decode (encodeFrom current xs) = decode current.toList ++ xs := by
  induction xs generalizing current with
  | nil => simp [encodeFrom]
  | cons x xs ih =>
    cases current with
    | none => simp only [encodeFrom, step]; rw [decode_append, ih]; simp [decode]
    | some r =>
      by_cases hv : r.value = x
      · simp only [encodeFrom, step, hv, if_true]; rw [decode_append, ih]
        simp [decode, List.replicate_succ', hv]
      · simp only [encodeFrom, step, hv, if_false]; rw [decode_append, ih]; simp [decode]

/-- Decoding an encoding gives back the input. -/
theorem decode_encode (xs : List Int) : decode (encode xs) = xs := by
  simpa [encode, decode] using decode_encodeFrom none xs

/-- Each run's value differs from the next run's. -/
def adjacentDiffer : List Run → Prop
  | a :: b :: l => a.value ≠ b.value ∧ adjacentDiffer (b :: l)
  | _ => True

/-- Encoding after the run `r` gives runs whose adjacent values differ, the
first with `r`'s value. -/
theorem encodeFrom_adjacentDiffer_head (r : Run) (xs : List Int) :
    adjacentDiffer (encodeFrom (some r) xs) ∧
      (encodeFrom (some r) xs).head?.map (·.value) = some r.value := by
  induction xs generalizing r with
  | nil => simp [encodeFrom, adjacentDiffer]
  | cons x xs ih =>
    by_cases hv : r.value = x
    · simpa [encodeFrom, step, hv] using ih { value := x, count := r.count + 1 }
    · obtain ⟨hc, hh⟩ := ih { value := x, count := 1 }
      simp only [encodeFrom, step, hv, if_false, Option.toList_some, List.singleton_append]
      refine ⟨?_, by simp⟩
      cases h : encodeFrom (some { value := x, count := 1 }) xs with
      | nil => simp [h] at hh
      | cons b l =>
        rw [h] at hc hh
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hh
        exact ⟨by rw [hh]; exact hv, hc⟩

/-- Adjacent runs hold different values, so the encoding never splits a run
in two. -/
theorem encode_adjacentDiffer (xs : List Int) : adjacentDiffer (encode xs) := by
  cases xs with
  | nil => simp [encode, encodeFrom, adjacentDiffer]
  | cons x xs =>
    simpa [encode, encodeFrom, step] using (encodeFrom_adjacentDiffer_head { value := x, count := 1 } xs).1

/-- Encoding after a run with at least one value gives runs with at least one
value each. -/
theorem encodeFrom_count (current : Option Run) (xs : List Int)
    (h : ∀ r ∈ current, 1 ≤ r.count) : ∀ r ∈ encodeFrom current xs, 1 ≤ r.count := by
  induction xs generalizing current with
  | nil => simpa [encodeFrom] using h
  | cons x xs ih =>
    intro r hr
    simp only [encodeFrom, List.mem_append] at hr
    rcases hr with hr | hr
    · cases current with
      | none => simp [step] at hr
      | some c => by_cases hv : c.value = x <;> simp_all [step]
    · refine ih _ ?_ r hr
      cases current with
      | none => simp [step]
      | some c => by_cases hv : c.value = x <;> simp [step, hv]

/-- Every run has at least one value. -/
theorem encode_count (xs : List Int) : ∀ r ∈ encode xs, 1 ≤ r.count :=
  encodeFrom_count none xs (by simp)

example :
    encode [7, 7, 3, 7] = [{ value := 7, count := 2 }, { value := 3, count := 1 }, { value := 7, count := 1 }] := by
  decide

end Rle
