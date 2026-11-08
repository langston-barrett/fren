module

import FrenBase.Binding
meta import FrenBase.Binding
meta import FrenProp

open FrenBase.Binding

-- These are laws of the production functions, linked to the existing chapter's
-- primitive contracts. No expression model or Plausible axiom is involved.
--@ reference: bindings.primitive.scope
example (ctx : Context Ty) (i : Nat) :
    lookup ctx i = none ↔ ¬ InScope ctx.length i := lookup_none_iff ctx i

--@ reference: bindings.primitive.shift
example (hi : InScope n i) (_hc : c ≤ n) :
    (i < c → shiftIndex a c i = i) ∧
    (c ≤ i → shiftIndex a c i = i + a) ∧ InScope (n + a) (shiftIndex a c i) :=
  ⟨shiftIndex_below, shiftIndex_above, shiftIndex_scoped hi⟩

--@ reference: bindings.primitive.lift
example (h : MapsInto n m ρ) : MapsInto (n + 1) (m + 1) (liftRen ρ) :=
  liftRen_scoped h

--@ reference: bindings.substitution.lift
example (var : Nat → α) (weaken : α → α) (σ : Nat → α) (i : Nat) :
    liftSub var weaken σ 0 = var 0 ∧
    liftSub var weaken σ (i + 1) = weaken (σ i) := ⟨rfl, rfl⟩

#print axioms lookup_none_iff
#print axioms hasType_scoped
#print axioms exists_hasType_iff
#print axioms shiftIndex_comp
#print axioms shiftIndex_injective
#print axioms liftRenN_scoped
#print axioms liftRenN_comp
#print axioms liftRenN_shift
#print axioms liftSub_scoped

meta section

open Plausible
open scoped Plausible.Decorations

private def check (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit := do
  let result ← Testable.checkIO p' { numInst := 600, maxSize := 40, randomSeed := some 100219 }
  IO.println s!"{name}: 600 samples, size 40, seed 100219, no discarded premises: {result}"
  match result with
  | .success _ => pure ()
  | _ => throw <| IO.userError s!"binding property failed: {name}"

private def reject (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit := do
  let result ← Testable.checkIO p' { numInst := 600, maxSize := 40, randomSeed := some 100220 }
  IO.println s!"mutation {name}, seed 100220: {result}"
  match result with
  | .failure _ _ _ => pure ()
  | _ => throw <| IO.userError s!"mutation was not falsified: {name}"

private abbrev shiftCases (f : Nat → Nat → Nat → Nat) (a c i : Nat) : Prop :=
  f a c i = if i < c then i else i + a

private abbrev renCases (up : (Nat → Nat) → Nat → Nat) (offset i : Nat) : Prop :=
  up (· + offset) i = if i = 0 then 0 else (i - 1 + offset) + 1

private abbrev subCases (up : (Nat → List Nat) → Nat → List Nat) (xs : List Nat) (i : Nat) : Prop :=
  up (fun j => xs ++ [j]) i =
    if i = 0 then [0] else (xs ++ [i - 1]).map (· + 1)

#eval check "shift primitive cases" <| ∀ (a c i : Nat), shiftCases shiftIndex a c i

#eval check "context lookup and typed membership" <| ∀ (ctx : List Nat) (entry i : Nat),
  lookup (entry :: ctx) 0 = some entry ∧
  lookup (entry :: ctx) (i + 1) = lookup ctx i ∧
  (lookup ctx i = none ↔ ctx.length ≤ i) ∧
  (HasType (entry :: ctx) 0 entry) ∧
  decide (HasType (entry :: ctx) 0 (entry + 1)) = false ∧
  lookup ctx ctx.length = none ∧
  decide (lookup ctx i = some entry → i < ctx.length) = true

#eval check "shift insertion, composition and nested cutoffs" <| ∀ (ctx : List Nat) (a b cc i k : Nat),
  let c := cc % (ctx.length + 1)
  let inserted := ctx.take c ++ List.replicate a 999 ++ ctx.drop c
  lookup inserted (shiftIndex a c i) = lookup ctx i ∧
  shiftIndex b c (shiftIndex a c i) = shiftIndex (a + b) c i ∧
  liftRenN k (shiftIndex a cc) i = shiftIndex a (cc + k) i

#eval check "renaming fresh and older" <| ∀ (offset i : Nat), renCases liftRen offset i

#eval check "renaming identity and composition on raw indices" <| ∀ (a b i k : Nat),
  let ρ := fun j => (j + a) % 17
  let η := fun j => j * b
  liftRenN k id i = i ∧
  liftRenN k (η ∘ ρ) i = liftRenN k η (liftRenN k ρ i)

-- Lists are a carrier with several references, not a term datatype: the caller
-- supplies both variable construction and a shift action on that carrier.
#eval check "generic substitution extension" <| ∀ (xs : List Nat) (i : Nat),
  subCases (liftSub List.singleton (List.map (shiftIndex 1 0))) xs i

private def assert (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw <| IO.userError name

/-- Count premises over exactly this Plausible-generated batch, checking both
accepted and rejected inputs. These counts are separate from checkIO above. -/
private def scopedBatch : IO Unit := do
  let batch : Gen (Array (Nat × Nat × Nat × Nat × Nat × List Nat)) := do
    let mut samples := #[]
    for _ in [:600] do
      samples := samples.push (← Gen.chooseNat, ← Gen.chooseNat, ← Gen.chooseNat,
        ← Gen.chooseNat, ← Gen.chooseNat, ← Gen.listOf Gen.chooseNat)
    return samples
  let .ok samples := ((runRandWith 100221 batch).run ⟨40⟩)
    | throw <| IO.userError "scope batch generation failed"
  let mut shiftYes := 0; let mut shiftNo := 0
  let mut renYes := 0; let mut renNo := 0
  let mut subYes := 0; let mut subNo := 0
  let mut empty := 0; let mut closed := 0; let mut openValue := 0
  let mut dangling := 0; let mut largeCutoff := 0; let mut nested := 0
  for (nn, mm, ii, cc, kk, xs) in samples do
    let n := nn % 8
    let m := mm % 8
    let i := ii % 12
    let c := cc % 12
    let k := kk % 6
    let ρ := fun j => (j + mm) % 11
    let σ := fun j => if j % 2 == 0 then [] else xs.map (· % 10)
    let within := fun bound (ys : List Nat) => ys.all (· < bound)
    if n == 0 then empty := empty + 1
    if !(i < n) then dangling := dangling + 1
    if c > n then largeCutoff := largeCutoff + 1
    if k > 1 then nested := nested + 1
    if i < n && c ≤ n then
      shiftYes := shiftYes + 1
      assert "shift scope" (shiftIndex mm c i < n + mm)
    else shiftNo := shiftNo + 1
    if (List.range n).all (fun j => ρ j < m) then
      renYes := renYes + 1
      assert "lifted bounded renaming" ((List.range (n + k)).all (fun j => liftRenN k ρ j < m + k))
    else renNo := renNo + 1
    if (List.range n).all (fun j => within m (σ j)) then
      subYes := subYes + 1
      if n > 0 then
        if (List.range n).all (fun j => (σ j).isEmpty) then closed := closed + 1
        else openValue := openValue + 1
      assert "lifted substitution scope" ((List.range (n + 1)).all
        (fun j => within (m + 1) (liftSub List.singleton (List.map (shiftIndex 1 0)) σ j)))
    else subNo := subNo + 1
    assert "raw lookup out of scope" (lookup (List.replicate n 42) (n + i) == none)
  IO.println s!"scope batch: 600 generated inputs, size 40, seed 100221; shift accepted={shiftYes} rejected={shiftNo}; renaming accepted={renYes} rejected={renNo}; substitution accepted={subYes} rejected={subNo}"
  IO.println s!"categories: empty contexts={empty}; dangling indices={dangling}; cutoffs past context={largeCutoff}; nested binders={nested}; accepted nonempty-source closed environments={closed}; accepted open environments={openValue}"
  assert "nonvacuous premise coverage" (shiftYes > 0 && shiftNo > 0 && renYes > 0 && renNo > 0 && subYes > 0 && subNo > 0)
  assert "nonvacuous categories" (empty > 0 && dangling > 0 && largeCutoff > 0 && nested > 0 && closed > 0 && openValue > 0)

#eval scopedBatch

#eval do
  assert "huge cutoff leaves raw index alone" (shiftIndex 7 100000000000000000000 99 == 99)
  assert "huge raw index moves" (shiftIndex 7 2 100000000000000000000 == 100000000000000000007)
  assert "zero scope is empty" (lookup ([] : Context Nat) 0 == none)
  assert "context identity is not length" (lookup [3] 0 != lookup [4] 0)
  assert "nested local slots protected" (liftRenN 4 (shiftIndex 3 0) 3 == 3)
  assert "older slot escapes binders" (liftRenN 4 (shiftIndex 3 0) 4 == 7)

-- Each control executes a wrong implementation against the same primitive
-- property as the real code, and must produce an actual Plausible failure.
#eval reject "strict cutoff changed to inclusive" <| ∀ (a c i : Nat),
  shiftCases (fun a c i => if i ≤ c then i else i + a) a c i

#eval reject "older renaming image fails to move" <| ∀ (offset i : Nat),
  renCases (fun ρ => fun | 0 => 0 | j + 1 => ρ j) offset i

#eval reject "replacement is not weakened" <| ∀ (xs : List Nat) (i : Nat),
  subCases (fun σ => fun | 0 => [0] | j + 1 => σ j) xs i

#eval reject "nested shift uses root cutoff" <| ∀ (a c i k : Nat),
  liftRenN k (shiftIndex a c) i = shiftIndex a c i
