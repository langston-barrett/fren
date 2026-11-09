module

public import FrenThirDesugar
public import FrenMir

public section
namespace FrenThirToMir
open FrenAst FrenModule FrenMir

abbrev Result := Except FrenDiag.Diagnostic

/-- Internal table mismatches are explicit failures, never omitted declarations.
The public producer takes the checked witness, not this helper's raw Typed. -/
private def declaration (t : Typed) (decl : Decl) : Result (Option Declaration) := do
  let scope := t.resolved.scope.id
  match decl with
  | .moduleDecl .. => return none
  | .enumDecl _ _ name _ variants _ _ =>
    let id := scope.named name.text
    return some (.enumeration ⟨id, decl, variants.map fun v => (id.named v.text, v)⟩)
  | .function _ _ name _ _ _ _ _ =>
    let id := scope.named name.text
    let some sig := t.signatures.find? (·.id == id)
      | throw (FrenHirToThir.failure name.span "MIR missing admitted signature")
    let some body := t.bodies.find? (fun b => b.owner == id && b.member.isNone)
      | throw (FrenHirToThir.failure name.span "MIR missing admitted definition")
    return some (.function ⟨sig, body⟩)
  | .expectation _ name params _ _ _ =>
    -- Reuse the actual annotation reader also for blocks with no typed bodies.
    let parameters ← FrenHirToThir.parameters t.resolved params
    let owner := scope.named name.text
    return some (.block ⟨owner, decl, parameters, FrenHirToThir.parameterContext parameters,
      t.bodies.filter (·.owner == owner)⟩)

/-- The sole public conversion input carries equality to actual checkWalking.
No execution, matching transformation or solver interpretation is performed. -/
def produce (p : FrenThirDesugar.Program) : Result Theory := do
  let .declarations decls := p.typed.resolved.document.root
    | throw (FrenHirToThir.failure p.input.scope.name.span "MIR expected admitted declarations")
  let mut declarations := #[]
  for decl in decls do
    if let some d ← declaration p.typed decl then
      declarations := declarations.push d
  return ⟨p.typed, declarations, declarations.flatMap fun d =>
    match d with | .block b => b.requests | _ => #[]⟩

/-- Admission failures precede conversion, with their original diagnostic. -/
def fromSource (file : FrenSource.FileId) (source : String) :
    Except FrenHirToThir.StaticFailure Theory := do
  let p ← FrenThirDesugar.fromSource file source
  (produce p).mapError FrenHirToThir.StaticFailure.typing

theorem retains (p : FrenThirDesugar.Program) (out : Theory) (h : produce p = .ok out) :
    out.source = p.typed := by
  unfold produce at h
  split at h
  · simp only [Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · cases Except.ok.inj h
      rfl
  · contradiction

/-- The real output requests come only from retained blocks, in declaration
order. Together with request_context this excludes foreign hypotheses. -/
theorem requests_from_blocks (p : FrenThirDesugar.Program) (out : Theory)
    (h : produce p = .ok out) :
    out.requests = out.declarations.flatMap (fun d =>
      match d with | .block b => b.requests | _ => #[]) := by
  unfold produce at h
  split at h
  · simp only [Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · cases Except.ok.inj h
      rfl
  · contradiction

theorem request_from_block (p : FrenThirDesugar.Program) (out : Theory)
    (h : produce p = .ok out) (r : CheckRequest) (hr : r ∈ out.requests) :
    ∃ b, Declaration.block b ∈ out.declarations ∧ r ∈ b.requests := by
  rw [requests_from_blocks p out h] at hr
  obtain ⟨d, hd, hr⟩ := Array.mem_flatMap.mp hr
  cases d with
  | enumeration e => simp at hr
  | function f => simp at hr
  | block b => exact ⟨b, hd, hr⟩

theorem admission (p : FrenThirDesugar.Program) (out : Theory) (h : produce p = .ok out) :
    FrenHirToThir.checkWalking p.input = .ok out.source := by
  rw [retains p out h]
  exact p.accepted

theorem deterministic (p : FrenThirDesugar.Program) (a b : Theory)
    (ha : produce p = .ok a) (hb : produce p = .ok b) : a = b :=
  Except.ok.inj (ha.symm.trans hb)

theorem rejected (file : FrenSource.FileId) (source : String) (d : FrenHirToThir.StaticFailure)
    (h : FrenThirDesugar.fromSource file source = .error d) :
    fromSource file source = .error d := by simp [fromSource, h, Bind.bind, Except.bind]

end FrenThirToMir
