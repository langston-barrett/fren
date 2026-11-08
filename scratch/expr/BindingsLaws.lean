module

import all scratch.expr.Prototype
meta import scratch.expr.Prototype
meta import FrenProp

open ExprPrototype

--@ reference: bindings.laws.scope
theorem substTop_open_scoped {p : Phase} {s b : Expr p}
    (hs : Scoped n s) (hb : Scoped (n + 1) b) : Scoped n (substTop s b) := by
  apply subst_scoped hb
  intro i hi
  cases i with
  | zero => exact hs
  | succ i => exact .var (by omega)

--@ reference: bindings.shift.cutoff
theorem shift_scoped {p : Phase} {t : Expr p}
    (ht : Scoped n t) : Scoped (n + a) (shift a c t) := by
  apply rename_scoped ht
  intro i hi
  split <;> omega

#print axioms substTop_open_scoped
#print axioms shift_scoped

meta section

open Plausible
open scoped Plausible.Decorations

private def v (i : Nat) : Expr p := .roll (.var i)
private def lit (i : Nat) : Expr p := .roll (.lit i)

/-- Bounded raw constructor coverage, not a production arbitrary instance.
Arrays include several children; indices are deliberately not scope-filtered. -/
private def raw (p : Phase) (code : List Nat) : Expr p :=
  (code.take 8).foldl (fun e k => match k % 7 with
    | 0 => lit k
    | 1 => v (k % 7)
    | 2 => .roll (.all e)
    | 3 => .roll (.letE (v (k % 3)) e)
    | 4 => .roll (.array #[e, v (k % 5), .roll (.array #[])])
    | 5 => .roll (.letE e (.roll (.all (v (k % 4)))))
    | _ => if h : HasSugar p then .roll (.sugar h e) else .roll (.all e)) (v 0)

/-- Mathematical substAt abbreviation, using the actual total substitution. -/
private def substAt (j : Nat) (s t : Expr p) : Expr p :=
  subst (fun i => if i < j then v i else if i = j then s else v (i - 1)) t

private def check (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit := do
  let result ← Testable.checkIO p' { numInst := 300, maxSize := 20, randomSeed := some 100207 }
  IO.println s!"{name}: 300 samples, maxSize 20, seed 100207, no discarded premises: {result}"
  match result with
  | .success _ => pure ()
  | _ => throw <| IO.userError s!"binding property failed: {name}"

private def phaseChecks (p : Phase) : IO Unit := do
  --@ reference: bindings.laws.composition
  check s!"composition {repr p}" <| ∀ (xs ys : List Nat) (k : Nat),
    let t := raw p xs
    let s := raw p ys
    let ρ := fun i => (i + k) % 7
    let η := fun i => i * 2
    let σ := fun i => if i % 2 == 0 then shift (i % 3) 0 s else v (i % 4)
    let τ := fun i => if i % 3 == 0 then t else v (i + 1)
    (rename id t == t) ∧ (subst v t == t) ∧
    (rename η (rename ρ t) == rename (η ∘ ρ) t) ∧
    (subst τ (subst σ t) == subst (fun i => subst τ (σ i)) t) ∧
    (rename ρ (subst σ t) == subst (fun i => rename ρ (σ i)) t) ∧
    (subst σ (rename ρ t) == subst (fun i => σ (ρ i)) t)
  --@ reference: bindings.laws.shift-substitution
  check s!"shift/substitution {repr p}" <| ∀ (xs ys : List Nat) (aa cc jj : Nat),
    let t := raw p xs
    let s := raw p ys
    let a := aa % 4
    let c := cc % 5
    let j := jj % 5
    let j' := if j < c then j else j + a
    let c' := if c ≤ j then c else c + 1
    shift a c (substAt j s t) == substAt j' (shift a c s) (shift a c' t)

private def assert (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw <| IO.userError name

private def scopeCounts : IO Unit := do
  let batch : Gen (Array (List Nat × Nat)) := do
    let mut xs := #[]
    for _ in [:300] do
      xs := xs.push (← Gen.listOf Gen.chooseNat, (← Gen.chooseNat) % 4)
    return xs
  let .ok samples := ((runRandWith 100208 batch).run ⟨20⟩)
    | throw <| IO.userError "scope sample generation failed"
  let mut accepted := 0
  let mut rejected := 0
  let mut openAccepted := 0
  for (xs, n) in samples do
    let t := raw .high xs
    if scopeCheck n t then
      accepted := accepted + 1
      if !scopeCheck 0 t then openAccepted := openAccepted + 1
      assert "generated scoped shift" (scopeCheck (n + 2) (shift 2 1 t))
    else rejected := rejected + 1
  IO.println s!"scope premises: accepted={accepted}, rejected={rejected}, open accepted={openAccepted}; 300 generated inputs, seed 100208"
  assert "scope coverage is nonvacuous" (accepted > 0 && rejected > 0 && openAccepted > 0)

private def controls : IO Unit := do
  let b : Expr .high := .roll (.all (v 1))
  assert "capture example" (substTop (v 0) b == b)
  assert "unlifted replacement differs" (substTop (v 0) b != .roll (.all (v 0)))
  assert "wrong deletion index differs"
    (shift 1 0 (substAt 0 (lit 7) (v 0 : Expr .high)) != substAt 0 (lit 7) (shift 1 0 (v 0)))
  assert "wrong source cutoff differs"
    (shift 1 1 (substAt 0 (lit 7) (v 1 : Expr .high)) != substAt 0 (lit 7) (shift 1 1 (v 1)))
  assert "let value outside binder" (!scopeCheck 0 (.roll (.letE (v 0) (v 0)) : Expr .high))
  assert "open does not mean ill scoped" (scopeCheck 1 b && !scopeCheck 0 b)
  IO.println "capture, wrong-index, wrong-cutoff, let and open-scope controls passed"

#eval do
  phaseChecks .high
  phaseChecks .low
  scopeCounts
  controls
