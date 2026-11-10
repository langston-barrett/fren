module

public import FrenAstToHir.Lookup

public section
namespace FrenAstToHir
open FrenAst FrenModule FrenBase

/-- Unsupported inputs have no invented catalogue code. -/
def unsupported (span : FrenSource.Span) (detail : String) : FrenDiag.Diagnostic :=
  ⟨none, "unsupported walking resolver input: " ++ detail, span⟩

private def distinct (previous : List Token) (token : Token) (what : String) :
    Except FrenDiag.Diagnostic Unit := do
  if previous.any (fun p => sameName p.text token.text) then
    throw ⟨some "F0213", s!"{what} `{token.text}` is defined multiple times", token.span⟩

/-- `Bool` and `Int` are reserved names (`syntax.name.reserved`): no
declaration, variant, parameter or member label is named by one, and no
`let` binds one. Collection and the body walk both check names with this. -/
def unreserved (name : Token) : Except FrenDiag.Diagnostic Unit := do
  if name.text == "Bool" || name.text == "Int" then
    throw ⟨some "F0212", s!"`{name.text}` is a built-in type and cannot be redefined", name.span⟩

private def parameters (params : Parameters) : Except FrenDiag.Diagnostic Unit := do
  let mut previous := []
  for param in params.values do
    unreserved param.name
    distinct previous param.name "parameter"
    previous := param.name :: previous

private def add (scope : Scope) (name : Token) (kind : ItemKind) :
    Except FrenDiag.Diagnostic Scope := do
  if let some previous := member scope scope.id name.text then
    let description := match previous.kind with
      | .enumeration => "an enum" | .function => "a function"
      | .expectation => "an expectation" | .constructor => "a variant"
    throw ⟨some "F0206", s!"the name `{name.text}` is already defined in module `{scope.name.text}` (as {description})", name.span⟩
  return {scope with items := scope.items.push ⟨scope.id.named name.text, name, kind⟩}

/-- A complete single-module collection precedes all annotation/body lookup.
Returns the first collection failure in declaration/member source order. -/
def collect (decls : Array Decl) (fallback : FrenSource.Span) :
    Except FrenDiag.Diagnostic Scope := do
  let some (Decl.moduleDecl _ _ path) := decls[0]?
    | throw (unsupported fallback "expected one leading module declaration")
  unless path.tail.isEmpty do
    throw (unsupported path.head.span "module name must have one segment")
  unreserved path.head
  let mut scope : Scope := ⟨ItemId.root.named path.head.text, path.head, #[]⟩
  for decl in decls.extract 1 decls.size do
    match decl with
    | .moduleDecl _ keyword _ =>
      throw (unsupported keyword.span "multiple modules")
    | .enumDecl _ _ name _ variants _ _ =>
      unreserved name
      scope ← add scope name .enumeration
      let owner := scope.id.named name.text
      let mut previous := []
      for variant in variants do
        unreserved variant
        distinct previous variant "variant"
        previous := variant :: previous
        scope := {scope with items := scope.items.push ⟨owner.named variant.text, variant, .constructor⟩}
    | .function _ _ name params _ _ _ _ =>
      unreserved name
      scope ← add scope name .function
      parameters params
    | .expectation _ name params _ members _ =>
      unreserved name
      scope ← add scope name .expectation
      parameters params
      let mut previous := params.values.toList.map (·.name)
      for m in members do
        unreserved m.label
        distinct previous m.label "label"
        previous := m.label :: previous
  return scope

end FrenAstToHir
