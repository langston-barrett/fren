module

public import FrenWalking

public section
namespace FrenThirDesugar
open FrenModule FrenHirToThir

/-- A walking program admitted by the actual producer, including both walking
validators. The whole typed value is retained, not reconstructed. -/
structure Program where
  input : Resolved
  typed : Typed
  accepted : checkWalking input = .ok typed

/-- The current walking language has no sugar. -/
@[expose] def desugar (p : Program) : Program := p

/-- Admission failure is returned before the identity stage can run. -/
def fromResolved (input : Resolved) : Except StaticFailure Program :=
  match h : checkWalking input with
  | .error d => .error d
  | .ok typed => .ok (desugar ⟨input, typed, h⟩)

/-- Parse and resolve before the same admitted boundary. -/
def fromSource (file : FrenSource.FileId) (source : String) : Except StaticFailure Program := do
  let doc ← (FrenParse.parseFile file source).mapError (fun e =>
    .typing ⟨none, "expected " ++ e.diagnostic.expected, e.diagnostic.span⟩)
  let resolved ← (FrenAstToHir.resolve doc).mapError StaticFailure.typing
  fromResolved resolved

theorem identity (p : Program) : desugar p = p := rfl

theorem retains (p : Program) : (desugar p).typed = p.typed := rfl

theorem static (p : Program) :
    check p.input = .ok (desugar p).typed ∧ WalkingCoverage (desugar p).typed ∧
      WalkingNonrecursive (desugar p).typed :=
  (walking_success p.input p.typed).1 p.accepted

theorem resolved_retained (p : Program) : (desugar p).typed.resolved = p.input ∧ Admitted p.input :=
  walking_retains p.input p.typed p.accepted

theorem rejected (input : Resolved) (d : StaticFailure) (h : checkWalking input = .error d) :
    fromResolved input = .error d := by
  unfold fromResolved
  split <;> simp_all

theorem admitted (p : Program) : checkWalking (desugar p).input = .ok (desugar p).typed :=
  p.accepted

theorem deterministic (input : Resolved) (a b : Program)
    (ha : fromResolved input = .ok a) (hb : fromResolved input = .ok b) : a = b :=
  Except.ok.inj (ha.symm.trans hb)

end FrenThirDesugar
