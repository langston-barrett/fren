module

public import FrenHirToThir.Nonrecursive

public section
namespace FrenHirToThir
open FrenModule

inductive StaticFailure where
  | typing (diagnostic : FrenDiag.Diagnostic)
  | validation (failure : WalkingFailure)
  deriving Repr, BEq

/-- Raw validation requires `check t.resolved = .ok t` as a precondition.
It returns Unit only; checkWalking/checkWalkingSource (in `FrenWalking`) are
the admitted public result boundaries, and checkWalkingTyped requires producer
evidence. -/
def validateWalking (t : Typed) : ValidationResult := do
  validateCoverage t
  validateNonrecursive t
  return ()

theorem validateWalking_iff (t : Typed) : validateWalking t = .ok () ↔
    WalkingCoverage t ∧ WalkingNonrecursive t := by
  simp only [validateWalking, WalkingCoverage, WalkingNonrecursive,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases validateCoverage t <;> cases validateNonrecursive t <;> simp

end FrenHirToThir
