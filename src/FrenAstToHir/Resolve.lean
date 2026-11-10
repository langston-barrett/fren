module

public import FrenAstToHir.Collect
public import FrenParse

public section
namespace FrenAstToHir
open FrenAst FrenModule

private def pathReference (scope : Scope) (ctx : Context) (role : Role) (path : Path) :
    Except FrenDiag.Diagnostic Reference := do
  let selected ← lookup scope ctx path
  let target ← category scope role path selected
  return ⟨.path path, role, target, ctx⟩

private def annotation (scope : Scope) (ty : Ty) : Except FrenDiag.Diagnostic Reference :=
  match ty with
  | .bool token => .ok ⟨.builtin token, .annotation, .boolType, []⟩
  | .int token => .ok ⟨.builtin token, .annotation, .intType, []⟩
  | .named path => pathReference scope [] .annotation path

private def parameterTypes (scope : Scope) (params : Parameters) :
    Except FrenDiag.Diagnostic (Array Reference) := do
  let mut refs := #[]
  for param in params.values do
    match param.annotation with
    | some (_, ty) => refs := refs.push (← annotation scope ty)
    | none => refs := refs.push ⟨.implicitBool param.name, .annotation, .boolType, []⟩
  return refs

/-- Depth fuel is the actual AST's terminal count plus one at the public call site.
Each recursive call visits a strict expression subtree and consumes one unit;
siblings share the incoming budget/context, not one another's local scopes.
Exhaustion is an explicit failure, never success with dropped references. -/
private def walk : Nat → Scope → Context → Expr →
    Except FrenDiag.Diagnostic (Array Reference)
  | 0, scope, _, e => .error (unsupported ((e.tokens.head?).getD scope.name).span "expression depth exhausted")
  | fuel + 1, scope, ctx, e => do
    match e with
    | .name path => return #[← pathReference scope ctx .expression path]
    | .bool _ _ | .integer _ _ => return #[]
    | .paren _ body _ | .unary _ _ body => walk fuel scope ctx body
    | .binary left _ _ right =>
      let first ← walk fuel scope ctx left
      return first ++ (← walk fuel scope ctx right)
    | .call callee _ args _ _ =>
      let mut refs ← walk fuel scope ctx callee
      for arg in args do refs := refs ++ (← walk fuel scope ctx arg)
      return refs
    | .ifE _ condition _ yes _ no =>
      let first ← walk fuel scope ctx condition
      let second ← walk fuel scope ctx yes
      return first ++ second ++ (← walk fuel scope ctx no)
    | .letE _ name _ value _ body =>
      unreserved name
      let first ← walk fuel scope ctx value
      return first ++ (← walk fuel scope (name :: ctx) body)
    | .matchE _ scrutinee _ arms _ =>
      let mut refs ← walk fuel scope ctx scrutinee
      for (path, _, body, _) in arms do
        refs := refs.push (← pathReference scope ctx .pattern path)
        refs := refs ++ (← walk fuel scope ctx body)
      return refs

private def body (scope : Scope) (ctx : Context) (expr : Expr) :=
  walk (expr.tokens.length + 1) scope ctx expr

/-- Validate external documents with the one existing grammar implementation.
This prevents a caller editing, truncating, dropping or fabricating AST nodes
from laundering that document into HIR. It is not a second grammar or an
assumed validity Boolean. Exact parser-produced file documents pass unchanged.
Moduleless contexts and expression roots are explicitly outside this API. -/
private def resolveReferences (doc : Document) :
    Except FrenDiag.Diagnostic (Scope × Array Reference) := do
  let fallback := (FrenSource.Span.checked doc.file 0 0 doc.source.utf8ByteSize).get
    ((FrenSource.Span.checked_some_iff doc.file 0 0 doc.source.utf8ByteSize).mpr ⟨by omega, by omega⟩)
  let .ok parsed := FrenParse.parseFile doc.file doc.source
    | throw (unsupported fallback "source does not parse as a complete file")
  unless parsed == doc do
    throw (unsupported fallback "document differs from the complete file parse")
  let .declarations decls := doc.root
    | throw (unsupported fallback "expected file declarations")
  let scope ← collect decls fallback
  let mut refs := #[]
  for decl in decls do
    match decl with
    | .moduleDecl .. | .enumDecl .. => pure ()
    | .function _ _ _ params _ result _ expr =>
      refs := refs ++ (← parameterTypes scope params)
      refs := refs.push (← annotation scope result)
      let ctx := params.values.toList.reverse.map (·.name)
      refs := refs ++ (← body scope ctx expr)
    | .expectation _ _ params _ members _ =>
      refs := refs ++ (← parameterTypes scope params)
      let ctx := params.values.toList.reverse.map (·.name)
      for m in members do refs := refs ++ (← body scope ctx m.body)
  return (scope, refs)

/-- Resolve every walking reference or return the first diagnostic. -/
def resolve (doc : Document) : Except FrenDiag.Diagnostic Resolved :=
  (resolveReferences doc).map fun (scope, refs) => ⟨doc, scope, refs⟩

/-- Functional determinism, not a whole-pass semantic correctness theorem. -/
theorem deterministic (doc : Document) (a b : Resolved)
    (ha : resolve doc = .ok a) (hb : resolve doc = .ok b) : a = b := by
  rw [ha] at hb
  exact Except.ok.inj hb

/-- Storage preservation is separate from the unproved coverage/traversal law. -/
theorem syntax_preserved (doc : Document) (result : Resolved)
    (h : resolve doc = .ok result) : result.document = doc := by
  unfold resolve at h
  cases hc : resolveReferences doc with
  | error error => simp [hc, Except.map] at h
  | ok pair =>
    simp [hc, Except.map] at h
    cases h
    rfl

/-- All written terminals, with their file/span/spelling data, are retained.
This does not assert complete resolved-reference coverage. -/
theorem terminals_preserved (doc : Document) (result : Resolved)
    (h : resolve doc = .ok result) : result.document.root.tokens = doc.root.tokens := by
  rw [syntax_preserved doc result h]

end FrenAstToHir
