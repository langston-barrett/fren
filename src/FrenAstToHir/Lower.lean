module

public import FrenAstToHir.Resolve

/-! The resolver's output in the IR core: `Resolved` (the syntax tree plus its
reference table) read into an HIR `Module` over `Expr .hir`. Every surface form
stays (parentheses included); names become de Bruijn indices or item ids, as
the reference table selected them. Each node's origin records the span of its
first token, each binder's and parameter's origin its name token. -/

public section
namespace FrenAstToHir.Lower
open FrenAst FrenModule FrenExpr
open FrenModule.Core (Param Enum Function Member Check Item Module Hir)

abbrev M := StateT (Array Origin) (Except FrenDiag.Diagnostic)

private def fallbackSpan (r : Resolved) : FrenSource.Span := r.scope.name.span

private def origin (span : FrenSource.Span) (name : Option String := none) : M OriginId :=
  modifyGet fun os => (os.size, os.push {span := some span, name})

private def fail (span : FrenSource.Span) (detail : String) : M α :=
  throw (unsupported span detail)

private def anchorSpan (r : Resolved) (e : FrenAst.Expr) : FrenSource.Span :=
  (e.tokens.head?.map (·.span)).getD (fallbackSpan r)

/-- The reference the resolver recorded at a token, with the expected role and
the exact lexical context the lowering is in. -/
private def referenceAt (r : Resolved) (ctx : List Token) (token : Token) (role : Role) : M Target := do
  let some ref := r.referenceAt token.slice | fail token.span "missing resolved occurrence"
  unless ref.role == role do fail token.span "wrong resolved occurrence role"
  unless ref.context == ctx do fail token.span "resolved context differs"
  pure ref.target

private theorem hir : Phase.Untyped .hir := rfl
private theorem hirSurface : Phase.Surface .hir := Or.inl rfl

/-- One depth unit per recursive edge, from the body's terminal count. -/
def expr (r : Resolved) : Nat → List Token → FrenAst.Expr → M (Expr .hir)
  | 0, _, e => fail (anchorSpan r e) "expression depth exhausted"
  | fuel + 1, ctx, e => do
    let o ← origin (anchorSpan r e)
    let mk (n : ExprF .hir (Expr .hir)) : Expr .hir := ⟨o, (), n⟩
    match e with
    | .bool _ v => pure (mk (.bool v))
    | .integer _ v => pure (mk (.int v))
    | .name path =>
      match ← referenceAt r ctx path.head .expression with
      | .local i => pure (mk (.var i))
      | .item id => pure (mk (.item hir id))
      | _ => fail path.head.span "type in expression position"
    | .paren _ body _ => pure (mk (.paren hirSurface (← expr r fuel ctx body)))
    | .unary _ op body => pure (mk (.unary op (← expr r fuel ctx body)))
    | .binary left _ op right => do
      let l ← expr r fuel ctx left
      pure (mk (.binary op l (← expr r fuel ctx right)))
    | .call (.name path) _ args _ _ => do
      let callee ← match ← referenceAt r ctx path.head .expression with
        | .local i => pure (Ref.local i)
        | .item id => pure (Ref.item id)
        | _ => fail path.head.span "type in callee position"
      let mut out := #[]
      for arg in args do out := out.push (← expr r fuel ctx arg)
      pure (mk (.apply hir callee out))
    | .call callee _ _ _ _ => fail (anchorSpan r callee) "callee is not a name"
    | .ifE _ c _ y _ n => do
      let c ← expr r fuel ctx c
      let y ← expr r fuel ctx y
      pure (mk (.ite c y (← expr r fuel ctx n)))
    | .letE _ name _ value _ body => do
      let v ← expr r fuel ctx value
      let b ← origin name.span (some name.text)
      let body ← expr r fuel (name :: ctx) body
      pure (mk (.letE ⟨b, name.text.endsWith "?"⟩ v body))
    | .matchE _ scrutinee _ arms _ => do
      let s ← expr r fuel ctx scrutinee
      let mut out := #[]
      for (path, _, body, _) in arms do
        let .item id ← referenceAt r ctx path.head .pattern
          | fail path.head.span "pattern is not an item"
        let po ← origin path.head.span
        out := out.push (⟨po, id⟩, ← expr r fuel ctx body)
      pure (mk (.matchE s out))

private def body (r : Resolved) (ctx : List Token) (e : FrenAst.Expr) : M (Expr .hir) :=
  expr r (e.tokens.length + 1) ctx e

private def annotation (r : Resolved) (token : Token) : M FrenExpr.Ty := do
  match ← referenceAt r [] token .annotation with
  | .boolType => pure .bool
  | .intType => pure .int
  | .item id => pure (.enum id)
  | .local _ => fail token.span "local type annotation"

private def params (r : Resolved) (ps : Parameters) : M (Array Param) :=
  ps.values.mapM fun p => do
    let o ← origin p.name.span (some p.name.text)
    let type ← match p.annotation with
      | some (_, .bool t) | some (_, .int t) => annotation r t
      | some (_, .named path) => annotation r path.head
      | none => annotation r p.name
    pure ⟨o, type, p.name.text.endsWith "?", p.annotation.isSome⟩

private def run (m : M α) : Except FrenDiag.Diagnostic (α × Array Origin) := m.run #[]

/-- Read a resolver result into an HIR module, in declaration order. -/
def lower (r : Resolved) : Except FrenDiag.Diagnostic Hir := do
  let .declarations decls := r.document.root
    | throw (unsupported (fallbackSpan r) "expected file declarations")
  let mut items : Array (Item (Expr .hir)) := #[]
  for decl in decls do
    match decl with
    | .moduleDecl .. => pure ()
    | .enumDecl _ _ name _ variants _ _ =>
      let id := r.scope.id.named name.text
      let ((), os) ← run (discard (origin name.span (some name.text)))
      items := items.push (.enum ⟨id, 0, variants.map (id.named ·.text)⟩ os)
    | .function _ _ name ps _ result _ e =>
      let ((ps, result, e), os) ← run do
        discard (origin name.span (some name.text))
        let ps ← params r ps
        let result ← match result with
          | .bool t | .int t => annotation r t
          | .named path => annotation r path.head
        pure (ps, result, ← body r (parameterTokens decl) e)
      items := items.push (.function ⟨r.scope.id.named name.text, 0, ps, result, e⟩ os)
    | .expectation _ name ps _ members _ =>
      let ((ps, members), os) ← run do
        discard (origin name.span (some name.text))
        let qs ← params r ps
        let members ← members.mapM fun m => do
          let o ← origin m.label.span (some m.label.text)
          let e ← body r (parameterTokens decl) m.body
          pure ({kind := m.kind, label := m.label.text, origin := o, body := e} : Member (Expr .hir))
        pure (qs, members)
      items := items.push (.check ⟨r.scope.id.named name.text, 0, ps, members⟩ os)
  pure ⟨r.scope.id, items⟩
where
  /-- Parameters extend the context in written order: the last is nearest. -/
  parameterTokens : Decl → List Token
    | .function _ _ _ ps _ _ _ _ | .expectation _ _ ps _ _ _ => ps.values.toList.reverse.map (·.name)
    | _ => []

/-- Resolve a document and read the result into the IR core. -/
def resolveModule (doc : Document) : Except FrenDiag.Diagnostic Hir := do
  lower (← resolve doc)

end FrenAstToHir.Lower
