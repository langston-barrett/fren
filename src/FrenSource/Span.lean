module

public import Lean

namespace FrenSource

/-- Caller-assigned identity of a source file. No global allocation is implied. -/
public structure FileId where
  value : Nat
  deriving Repr, DecidableEq, BEq

/-- A half-open range of UTF-8 byte offsets in a file. Bounds checking does not
ensure that either endpoint lies on a Unicode character boundary. -/
public structure Span where private mk ::
  file : FileId
  start : Nat
  stop : Nat
  deriving Repr, DecidableEq, BEq

namespace Span

/-- Check both ordering and the supplied file size, in bytes. -/
public def checked (file : FileId) (start stop size : Nat) : Option Span :=
  if start ≤ stop ∧ stop ≤ size then some ⟨file, start, stop⟩ else none

public theorem checked_some_iff (file : FileId) (start stop size : Nat) :
    (checked file start stop size).isSome = true ↔ start ≤ stop ∧ stop ≤ size := by
  simp [checked]

public theorem checked_getters (file : FileId) (start stop size : Nat) (s : Span)
    (h : checked file start stop size = some s) :
    s.file = file ∧ s.start = start ∧ s.stop = stop := by
  simp only [checked] at h
  split at h
  next => cases h; exact ⟨rfl, rfl, rfl⟩
  next => simp at h

public theorem checked_reversed (file : FileId) (start stop size : Nat) (h : stop < start) :
    checked file start stop size = none := by
  simp [checked, Nat.not_le_of_gt h]

public theorem checked_outside (file : FileId) (start stop size : Nat) (h : size < stop) :
    checked file start stop size = none := by
  simp [checked, Nat.not_le_of_gt h]

/-- Translate a body-relative span into a host file. The caller supplies the
unchanged body's byte length and host start and size; checking these numbers
cannot establish that extraction actually preserved the body. -/
public def offset (s : Span) (bodySize : Nat) (host : FileId)
    (hostStart hostSize : Nat) : Option Span :=
  if s.start ≤ s.stop ∧ s.stop ≤ bodySize ∧ hostStart + bodySize ≤ hostSize then
    checked host (hostStart + s.start) (hostStart + s.stop) hostSize
  else none

public theorem offset_of_bounds (s : Span) (bodySize : Nat) (host : FileId)
    (hostStart hostSize : Nat) (ordered : s.start ≤ s.stop)
    (within : s.stop ≤ bodySize) (hostWithin : hostStart + bodySize ≤ hostSize) :
    (offset s bodySize host hostStart hostSize).isSome = true := by
  simp [offset, checked, ordered, within, hostWithin,
    Nat.le_trans (Nat.add_le_add_left within hostStart) hostWithin]

public theorem offset_getters (s result : Span) (bodySize : Nat) (host : FileId)
    (hostStart hostSize : Nat) (h : offset s bodySize host hostStart hostSize = some result) :
    result.file = host ∧ result.start = hostStart + s.start ∧
      result.stop = hostStart + s.stop ∧ result.start ≤ result.stop ∧
      result.stop - result.start = s.stop - s.start := by
  simp only [offset] at h
  split at h
  next bounds =>
    have getters := checked_getters host (hostStart + s.start) (hostStart + s.stop) hostSize result h
    rcases getters with ⟨hf, hs, he⟩
    refine ⟨hf, hs, he, ?_, ?_⟩
    · rw [hs, he]; exact Nat.add_le_add_left bounds.1 hostStart
    · rw [hs, he]; exact Nat.add_sub_add_left _ _ _
  next => simp at h

end Span
end FrenSource
