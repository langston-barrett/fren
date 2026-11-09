module

public import FrenLirToOir.Questions
public import FrenFlatToLir

public section
namespace FrenLirToOir
open FrenOir

private def extract (lir : FrenLir.Program) : Result Program := do
  let enumerations := lir.declarations.filterMap fun d => match d with
    | .enumeration e => some e
    | _ => none
  let definitions := lir.declarations.filterMap fun d => match d with
    | .function sig b => some (Definition.mk sig b)
    | _ => none
  let qs ← questions lir definitions
  return ⟨lir, enumerations, definitions, qs⟩

/-- The only root producer runs the actual LIR producer on an accepted source
witness. An edited logical program or a supplied success bit is not an input. -/
def produce (p : FrenThirDesugar.Program) : Result Program := do
  let lir ← (FrenFlatToLir.produce p).mapError Failure.lowering
  extract lir

inductive SourceFailure where
  | admission (diagnostic : FrenHirToThir.StaticFailure)
  | generation (failure : Failure)
  deriving Repr

def fromSource (file : FrenSource.FileId) (source : String) :
    Except SourceFailure Program := do
  let p ← (FrenThirDesugar.fromSource file source).mapError SourceFailure.admission
  (produce p).mapError SourceFailure.generation

theorem deterministic (p : FrenThirDesugar.Program) (a b : Program)
    (ha : produce p = .ok a) (hb : produce p = .ok b) : a = b :=
  Except.ok.inj (ha.symm.trans hb)

theorem retains_lir (p : FrenThirDesugar.Program) (out : Program) (h : produce p = .ok out) :
    FrenFlatToLir.produce p = .ok out.lir := by
  unfold produce at h
  cases hl : FrenFlatToLir.produce p with
  | error d => simp [hl, Except.mapError, Bind.bind, Except.bind] at h
  | ok lir =>
    simp only [hl, Except.mapError, Bind.bind, Except.bind] at h
    unfold extract at h
    simp only [Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · cases Except.ok.inj h
      rfl

/-- Every function, including unused ones, retains both actual equations. -/
theorem retained_equations (p : FrenThirDesugar.Program) (out : Program) (h : produce p = .ok out) :
    out.definitions = out.lir.declarations.filterMap (fun d => match d with
      | .function sig b => some (Definition.mk sig b)
      | _ => none) := by
  unfold produce at h
  cases hl : FrenFlatToLir.produce p with
  | error d => simp [hl, Except.mapError, Bind.bind, Except.bind] at h
  | ok lir =>
    simp only [hl, Except.mapError, Bind.bind, Except.bind] at h
    unfold extract at h
    simp only [Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · cases Except.ok.inj h
      rfl

theorem lowering_rejected (p : FrenThirDesugar.Program) (d : FrenDiag.Diagnostic)
    (h : FrenFlatToLir.produce p = .error d) : produce p = .error (.lowering d) := by
  simp [produce, h, Except.mapError, Bind.bind, Except.bind]

theorem admission (p : FrenThirDesugar.Program) (out : Program) (h : produce p = .ok out) :
    FrenHirToThir.checkWalking p.input = .ok out.lir.mir.source :=
  FrenFlatToLir.admission p out.lir (retains_lir p out h)

theorem retains_source (p : FrenThirDesugar.Program) (out : Program) (h : produce p = .ok out) :
    out.lir.mir.source = p.typed :=
  FrenFlatToLir.retains_source p out.lir (retains_lir p out h)

theorem scoped_input (p : FrenThirDesugar.Program) (out : Program) (h : produce p = .ok out) :
    out.lir.wellFormed = true :=
  FrenFlatToLir.wellFormed p out.lir (retains_lir p out h)

end FrenLirToOir
