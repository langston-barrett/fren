module

public import FrenModule.Typed
public import FrenAstToHir

public section
namespace FrenHirToThir
open FrenAst FrenModule FrenExpr

abbrev Result := Except FrenDiag.Diagnostic

@[expose] def failure (span : FrenSource.Span) (detail : String) : FrenDiag.Diagnostic :=
  ⟨none, "walking type error: " ++ detail, span⟩

@[expose] def mismatch (span : FrenSource.Span) (expected found : FrenExpr.Ty) : FrenDiag.Diagnostic :=
  ⟨some "F0304", s!"type mismatch: expected `{expected.display}`, found `{found.display}`", span⟩

@[expose] def requireType (span : FrenSource.Span) (expected found : FrenExpr.Ty) : Result Unit :=
  if found.compatible expected then .ok () else .error (mismatch span expected found)

@[expose] def anchor (e : Expr) (fallback : Token) : Token := e.tokens.head?.getD fallback

@[expose] def reference (input : Resolved) (token : Token) (role : Role) : Result Reference := do
  let some ref := input.referenceAt token.slice
    | throw (failure token.span "missing resolved occurrence")
  unless ref.role == role do throw (failure token.span "wrong resolved occurrence role")
  return ref

@[expose] def annotation (input : Resolved) (ty : FrenAst.Ty) : Result FrenExpr.Ty := do
  let token := match ty with | .bool t | .int t => t | .named p => p.head
  let ref ← reference input token .annotation
  match ref.target with
  | .boolType => return .bool
  | .intType => return .int
  | .item id => return .enum id
  | .local _ => throw (failure token.span "local type annotation")

@[expose] def suffix (name : Token) (ty : FrenExpr.Ty) : Result Unit :=
  if name.text.endsWith "?" then requireType name.span .bool ty else .ok ()

@[expose] def parameters (input : Resolved) (params : Parameters) : Result (Array TypedParameter) := do
  let mut typed := #[]
  for p in params.values do
    let ty ← match p.annotation with
      | some (_, ty) => annotation input ty
      | none => do
        let r ← reference input p.name .annotation
        unless r.target == .boolType && p.name.text.endsWith "?" do
          throw (failure p.name.span "omitted annotation requires a Bool suffix")
        pure .bool
    suffix p.name ty
    typed := typed.push ⟨p, ty⟩
  return typed

@[expose] def parameterContext (params : Array TypedParameter) : TypeContext :=
  params.toList.reverse.map fun p => (p.written.name, p.type)

@[expose] def signatures (input : Resolved) : Result (Array Signature) := do
  let .declarations decls := input.document.root
    | throw (failure input.scope.name.span "expected declarations")
  let mut sigs := #[]
  for decl in decls do
    match decl with
    | .function _ _ name params _ result _ _ =>
      sigs := sigs.push ⟨input.scope.id.named name.text, ← parameters input params,
        ← annotation input result, result⟩
    | .expectation _ _ params _ _ _ => discard <| parameters input params
    | _ => pure ()
  return sigs

@[expose] def signatureAt (sigs : Array Signature) (id : FrenBase.ItemId) : Option Signature :=
  sigs.find? (·.id == id)

/-- Only a collected constructor supplies a value type; its parent is its
canonical owner. Admission ensures the collected items came from the AST. -/
@[expose] def constructorType (input : Resolved) (id : FrenBase.ItemId) : Option FrenExpr.Ty := do
  let item ← input.scope.items.find? (·.id == id)
  if item.kind != .constructor then none else return .enum (← id.parent)

@[expose] def localType (ctx : TypeContext) (i : Nat) : Option FrenExpr.Ty :=
  (FrenBase.Binding.lookup ctx i).map Prod.snd

theorem localType_entry (ctx : TypeContext) (i : Nat) (token : Token) (ty : FrenExpr.Ty)
    (h : FrenBase.Binding.HasType ctx i (token, ty)) : localType ctx i = some ty := by
  unfold localType
  rw [h]
  rfl

end FrenHirToThir
