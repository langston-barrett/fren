module

public import FrenHirToThir
public import FrenAstToHir

/-! The walking skeleton's admitted boundary over the legacy `Resolved`
representation. Admission re-runs the resolver on the retained document, and
`checkSource` runs the parser and resolver first, so this adapter, not the
`FrenHirToThir` pass, depends on upstream passes. Names stay in the
`FrenHirToThir` namespace so that downstream walking passes are unchanged.
The pass proper is `FrenHirToThir.Pass.typeModule`, over the IR core. -/

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

/-- Actual typing after the checked producer boundary. Both named walking
validators remain outstanding, even for a successfully typed result. -/
@[expose] def check (input : Resolved) : Result Typed := do
  let admitted ← admit input
  typeResolved admitted.val

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
  simp only [Bind.bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i a ha
    have he := admit_retains input a ha
    exact ⟨(typeResolved_retains _ _ h).trans he, he ▸ a.property⟩

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

end FrenHirToThir
