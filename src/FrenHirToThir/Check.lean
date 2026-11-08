module

public import FrenHirToThir.Walk

public section
namespace FrenHirToThir
open FrenAst FrenModule

/-- The same concrete relation as Spec.Compiler.Thir.Admitted. Equality covers
all fields, not just targets or a supplied validity Boolean. -/
@[expose] def Admitted (input : Resolved) : Prop := FrenAstToHir.resolve input.document = .ok input

/-- The producer retains the exact supplied document (syntax_preserved).
Only the flat collected scope and reference table need decidable equality;
no nested AST equality axiom or second name lookup is introduced. -/
@[expose] def admit (input : Resolved) : Result {r : Resolved // Admitted r} :=
  match h : FrenAstToHir.resolve input.document with
  | .error _ => .error (failure input.scope.name.span "incoherent resolved input")
  | .ok produced =>
    if same : produced.scope = input.scope ∧ produced.references = input.references then
      .ok ⟨input, by
        have hd := FrenAstToHir.syntax_preserved input.document produced h
        have hs := same.1
        have hr := same.2
        have he : produced = input := by cases produced; cases input; simp_all
        exact he ▸ h⟩
    else .error (failure input.scope.name.span "incoherent resolved input")

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

/-- Actual typing after the checked producer boundary. Both named walking
validators remain outstanding, even for a successfully typed result. -/
@[expose] def check (input : Resolved) : Result Typed := do
  let admitted ← admit input
  let sigs ← signatures admitted.val
  let typedBodies ← bodies admitted.val sigs
  return ⟨admitted.val, sigs, typedBodies⟩

/-- Small convenience entry for the actual parse/resolve/type pipeline. Parse
failures retain the parser's diagnostic; resolver failures retain theirs. -/
@[expose] def checkSource (file : FrenSource.FileId) (source : String) : Result Typed := do
  let doc ← (FrenParse.parseFile file source).mapError (fun e =>
    ⟨none, "expected " ++ e.diagnostic.expected, e.diagnostic.span⟩)
  let resolved ← FrenAstToHir.resolve doc
  check resolved

theorem admitted_producer (input : Resolved) (h : Admitted input) :
    ∃ r, admit input = .ok r ∧ r.val = input := by
  refine ⟨⟨input, h⟩, ?_, rfl⟩
  have hp : FrenAstToHir.resolve input.document = .ok input := h
  unfold admit
  split
  · rename_i d hd
    rw [hp] at hd
    contradiction
  · rename_i produced hd
    have he : produced = input := Except.ok.inj (hd.symm.trans hp)
    subst produced
    split
    · rfl
    · rename_i hn
      exact (hn ⟨rfl, rfl⟩).elim

theorem admit_retains (input : Resolved) (r : {r : Resolved // Admitted r})
    (h : admit input = .ok r) : r.val = input := by
  unfold admit at h
  split at h
  · contradiction
  · split at h
    · cases Except.ok.inj h; rfl
    · contradiction

theorem check_retains (input : Resolved) (out : Typed) (h : check input = .ok out) :
    out.resolved = input ∧ Admitted input := by
  unfold check at h
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  split at h
  · contradiction
  · rename_i a ha
    have he := admit_retains input a ha
    have had : Admitted input := he ▸ a.property
    split at h
    · contradiction
    · split at h
      · contradiction
      · cases Except.ok.inj h
        exact ⟨he, had⟩

/-- Equality of erasure includes the complete document, identities, targets,
lexical contexts, written order, and UTF-8 spans. -/
theorem erasure (input : Resolved) (out : Typed) (h : check input = .ok out) :
    out.resolved.document = input.document ∧ out.resolved.references = input.references ∧
      out.resolved.scope = input.scope := by
  rw [(check_retains input out h).1]
  exact ⟨rfl, rfl, rfl⟩

theorem deterministic (input : Resolved) (a b : Typed)
    (ha : check input = .ok a) (hb : check input = .ok b) : a = b :=
  Except.ok.inj (ha.symm.trans hb)

theorem requireType_iff (span : FrenSource.Span) (expected found : FrenExpr.Ty) :
    requireType span expected found = .ok () ↔ found = expected := by
  simp [requireType, FrenExpr.ValueType.compatible_iff]

end FrenHirToThir
