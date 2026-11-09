module

public import FrenHirToThir.Walk

public section
namespace FrenHirToThir
open FrenAst FrenModule

@[expose] def bodies (input : Resolved) (sigs : Array Signature) : Result (Array TypedBody) := do
  let .declarations decls := input.document.root
    | throw (failure input.scope.name.span "expected declarations")
  let mut out := #[]
  for decl in decls do
    match decl with
    | .function _ _ name _ _ _ _ expr =>
      let id := input.scope.id.named name.text
      let some sig := signatureAt sigs id | throw (failure name.span "missing function signature")
      let ctx := parameterContext sig.parameters
      let result ← infer (expr.tokens.length + 1) input sigs ctx expr false
      let ty ← result.value (anchor expr name).span
      requireType (anchor expr name).span sig.result ty
      out := out.push ⟨id, none, expr, ctx, ty, result.occurrences⟩
    | .expectation _ name params _ members _ =>
      let ctx := parameterContext (← parameters input params)
      for m in members do
        let result ← infer (m.body.tokens.length + 1) input sigs ctx m.body false
        let ty ← result.value (anchor m.body name).span
        requireType (anchor m.body name).span .bool ty
        out := out.push ⟨input.scope.id.named name.text, some m, m.body, ctx, ty, result.occurrences⟩
    | _ => pure ()
  return out

/-- Legacy typing of a `Resolved` record as it stands, with no admission:
signatures, then every body. It trusts the reference table it reads (each
lookup still fails on a missing, wrong-role or wrong-context reference). The
admitted boundary, which re-runs the resolver, is `check` in `FrenWalking`. -/
@[expose] def typeResolved (input : Resolved) : Result Typed := do
  let sigs ← signatures input
  let typedBodies ← bodies input sigs
  return ⟨input, sigs, typedBodies⟩

theorem typeResolved_retains (input : Resolved) (out : Typed) (h : typeResolved input = .ok out) :
    out.resolved = input := by
  unfold typeResolved at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · cases Except.ok.inj h; rfl

theorem requireType_iff (span : FrenSource.Span) (expected found : FrenExpr.Ty) :
    requireType span expected found = .ok () ↔ found = expected := by
  simp [requireType, FrenExpr.ValueType.compatible_iff]

end FrenHirToThir
