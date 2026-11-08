module

meta import FrenSource
meta import FrenSourceTests
meta import FrenProp

meta section

open FrenSource Plausible
open scoped Plausible.Decorations

def check (label : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit := do
  let result ← Testable.checkIO p' { numInst := 500, maxSize := 40, randomSeed := some 73291 }
  IO.println s!"{label} (500 generated cases (category by construction), seed 73291): {result}"
  match result with
  | .success _ => pure ()
  | _ => throw <| IO.userError s!"source span property failed or gave up: {label}"

#eval check "valid and offset" <| ∀ (file lo width extra : Nat),
  let hi := lo + width
  let size := hi + extra
  let hostStart := 100
  let hostSize := hostStart + size
  let span := Span.checked ⟨file⟩ lo hi size
  span.map (fun s => (s.file, s.start, s.stop)) = some (⟨file⟩, lo, hi) ∧
  (span.bind fun s => s.offset size ⟨file + 1⟩ hostStart hostSize).map
    (fun s => (s.file, s.start, s.stop)) = some (⟨file + 1⟩, hostStart + lo, hostStart + hi)

#eval check "reversed" <| ∀ (file lo size : Nat),
  Span.checked ⟨file⟩ (lo + 1) lo size = none

#eval check "out of bounds" <| ∀ (file size extra : Nat),
  Span.checked ⟨file⟩ 0 (size + extra + 1) size = none

#eval check "empty EOF" <| ∀ (file size : Nat),
  (Span.checked ⟨file⟩ size size size).map (fun s => (s.file, s.start, s.stop)) =
    some (⟨file⟩, size, size)

#eval FrenSourceTests.run
