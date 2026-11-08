module

public import FrenHirToThirTests.Support
import Plausible

public section
namespace FrenHirToThirTests
open FrenAst FrenModule FrenHirToThir FrenExpr Plausible
open scoped Plausible.Decorations

/-- Small recursive source trees, not a second IR/typechecker. Every branch
has a known Int result; targeted perturbations require rejected traversals. -/
private def tree : Nat → Nat → String
  | 0, n => if n % 2 == 0 then "x" else toString (n % 23)
  | depth + 1, n =>
    let a := tree depth (n / 3)
    let b := tree depth (n / 3 + 7)
    match n % 5 with
    | 0 => s!"({a} + {b})"
    | 1 => s!"(if true then {a} else {b})"
    | 2 => s!"(let x := {a} in {b})"
    | 3 => s!"(match E::A \{ E::A => {a}, E::B => {b} })"
    | _ => s!"(let b? := false in if b? then {a} else {b})"

structure Counts where
  admission : Nat := 0
  rejectedAdmission : Nat := 0
  signatures : Nat := 0
  rejectedSignature : Nat := 0
  lookupHit : Nat := 0
  lookupMiss : Nat := 0
  success : Nat := 0
  failure : Nat := 0
  deriving Repr

private def sample (n file : Nat) : Option Counts := do
  let good := tree (n % 3 + 1) n
  let prelude := "mod m\nenum E { A, B }\nfn f(x: Int): Int := "
  let sources := [(prelude ++ good, true, true), (prelude ++ "x", true, true),
    (prelude ++ s!"if true then {good} else false", true, false),
    (prelude ++ "match E::A {}", true, false),
    ("mod m\nfn f(b?: Int): Int := b?", false, false)]
  let mut counts : Counts := {}
  for (source, signatureOK, success) in sources do
    let .ok doc := FrenParse.parseFile ⟨file⟩ source | none
    let .ok r := FrenAstToHir.resolve doc | none
    let .ok a := admit r | none
    if a.val != r then none else pure ()
    counts := {counts with admission := counts.admission + 1}
    match signatures r with
    | .ok _ =>
      if !signatureOK then none else pure ()
      counts := {counts with signatures := counts.signatures + 1}
    | .error _ =>
      if signatureOK then none else pure ()
      counts := {counts with rejectedSignature := counts.rejectedSignature + 1}
    match check r with
    | .ok t =>
      if !success || !localsRetained t || t.resolved != r || t.bodies.size != 1 ||
          (t.bodies[0]?).map (·.type) != some .int then none else pure ()
      counts := {counts with success := counts.success + 1}
      for b in t.bodies do
        for o in nameOccurrences b do
          if let .name p := o.expression then
            if let some ref := r.referenceAt p.head.slice then
              if let .local i := ref.target then
                let some ty := localType o.context i | none
                if o.type != .value ty then none else pure ()
                counts := {counts with lookupHit := counts.lookupHit + 1}
                if (localType o.context o.context.length).isSome then none else pure ()
                counts := {counts with lookupMiss := counts.lookupMiss + 1}
    | .error d =>
      if success || d.headline.isEmpty then none else pure ()
      counts := {counts with failure := counts.failure + 1}
    -- An actual partial public table must fail admission, including a table
    -- from an ill-typed body. No supplied Boolean exempts this control.
    if (check {r with references := #[]}).isOk then none else pure ()
    counts := {counts with rejectedAdmission := counts.rejectedAdmission + 1}
  return counts

private def audit (n file : Nat) : Bool :=
  match sample n file with
  | none => false
  | some c => c.admission == 5 && c.rejectedAdmission == 5 && c.signatures == 4 &&
    c.rejectedSignature == 1 && c.success == 2 && c.failure == 3 && c.lookupHit > 0 && c.lookupMiss > 0

private def checkProperty (p : Prop)
    (decorated : Decorations.DecorationsOf p := by mk_decorations) [Testable decorated] : IO Unit := do
  let report ← Testable.checkIO decorated {numInst := 100, maxSize := 40, randomSeed := some 20261109}
  IO.println s!"actual walking typing Plausible: {report}"
  match report with
  | .success _ => pure ()
  | _ => throw (IO.userError "walking checker Plausible failure")

/-- Sampled laws about the actual recursive checker. Zero discarded premises;
each generated sample must include success, typing failure and admission failure. -/
def runProperties : IO Unit := do
  checkProperty <| ∀ (n file : Nat), audit n file = true
  let mut totals : Counts := {}
  for n in [:24] do
    let some c := sample n 93 | throw (IO.userError s!"typed census failed at {n}")
    totals := ⟨totals.admission + c.admission, totals.rejectedAdmission + c.rejectedAdmission,
      totals.signatures + c.signatures, totals.rejectedSignature + c.rejectedSignature,
      totals.lookupHit + c.lookupHit, totals.lookupMiss + c.lookupMiss,
      totals.success + c.success, totals.failure + c.failure⟩
  require (totals.admission == 120 && totals.rejectedAdmission == 120 && totals.signatures == 96 &&
    totals.rejectedSignature == 24 && totals.success == 48 && totals.failure == 72 &&
    totals.lookupHit > 0 && totals.lookupMiss > 0) "actual typing census vacuous"
  IO.println s!"actual generated traversal census (explicit stage probes, not internal call instrumentation): {repr totals}; discarded=0; finite samples, no universal soundness claim"

end FrenHirToThirTests
