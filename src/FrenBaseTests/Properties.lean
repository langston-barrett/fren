module

meta import FrenBase
meta import FrenBaseTests
meta import FrenProp

meta section

open FrenBase Plausible
open scoped Plausible.Decorations

def path (names : List String) : ItemId :=
  names.foldl (fun p n => ItemId.generated (ItemId.named p n) n n.length) .root

def check (p : Prop) (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit := do
  let result ← Testable.checkIO p' { numInst := 500, maxSize := 40, randomSeed := some 83917 }
  IO.println s!"identity properties (500 generated samples, seed 83917): {result}"
  match result with
  | .success _ => pure ()
  | _ => throw <| IO.userError "Plausible identity properties failed or gave up"

#eval check <| ∀ (names : List String) (name kind : String) (i : Nat),
  let p := path names
  (ItemId.named p name).parent = some p ∧
  (ItemId.named p name).component = some (.named name) ∧
  (ItemId.generated p kind i).parent = some p ∧
  (ItemId.generated p kind i).component = some (.generated kind i) ∧
  (ItemId.generated p kind i).components = p.components ++ [.generated kind i] ∧
  ItemId.named p name ≠ ItemId.generated p kind i ∧
  ItemId.generated p kind i ≠ ItemId.generated p kind (i + 1)


#eval FrenBaseTests.run
