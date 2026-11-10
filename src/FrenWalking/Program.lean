module

public import FrenWalking.Walking

/-! The walking pipeline's admitted program: a `Resolved` input with the
legacy checker's result and the evidence that both walking validators accepted
it. Every pass after type checking still consumes this value. It is not the
desugaring pass, which is `FrenThirDesugar` over the THIR module; it goes away
with the legacy checker (see `docs/fren2-walking-removal.md`). -/

public section
namespace FrenWalking
open FrenModule FrenHirToThir

/-- A walking program admitted by the actual producer, including both walking
validators. The whole typed value is retained, not reconstructed. -/
structure Program where
  input : Resolved
  typed : Typed
  accepted : checkWalking input = .ok typed

/-- Admission failure is returned and no program is built. -/
def fromResolved (input : Resolved) : Except StaticFailure Program :=
  match h : checkWalking input with
  | .error d => .error d
  | .ok typed => .ok ⟨input, typed, h⟩

/-- Parse and resolve before the same admitted boundary. -/
def fromSource (file : FrenSource.FileId) (source : String) : Except StaticFailure Program := do
  let doc ← (FrenParse.parseFile file source).mapError (fun e =>
    .typing ⟨none, "expected " ++ e.diagnostic.expected, e.diagnostic.span⟩)
  let resolved ← (FrenAstToHir.resolve doc).mapError StaticFailure.typing
  fromResolved resolved

theorem static (p : Program) :
    check p.input = .ok p.typed ∧ WalkingCoverage p.typed ∧ WalkingNonrecursive p.typed :=
  (walking_success p.input p.typed).1 p.accepted

theorem resolved_retained (p : Program) : p.typed.resolved = p.input ∧ Admitted p.input :=
  walking_retains p.input p.typed p.accepted

theorem rejected (input : Resolved) (d : StaticFailure) (h : checkWalking input = .error d) :
    fromResolved input = .error d := by
  unfold fromResolved
  split <;> simp_all

theorem deterministic (input : Resolved) (a b : Program)
    (ha : fromResolved input = .ok a) (hb : fromResolved input = .ok b) : a = b :=
  Except.ok.inj (ha.symm.trans hb)

end FrenWalking
