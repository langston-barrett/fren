module

public import FrenModule

public section
namespace FrenAstToHir
open FrenAst FrenModule FrenBase

/-- Same-scope duplicate decision, shared by collection's list checks. -/
@[expose] def sameName (first second : String) : Bool := first == second

/-- First equal spelling, in a nearest-first context. -/
@[expose] def nearest : List String → String → Option Nat
  | [], _ => none
  | name :: rest, query =>
    if name = query then some 0 else (nearest rest query).map (· + 1)

def localIndex (ctx : Context) (query : String) : Option Nat :=
  nearest (ctx.map (·.text)) query

def member (scope : Scope) (parent : ItemId) (name : String) : Option Item :=
  scope.items.find? (fun item => item.id == parent.named name)

inductive Selection where
  | moduleSelf | item (value : Item) | local (index : Nat)
  deriving Repr, BEq

def Selection.target (scope : Scope) : Selection → Target
  | .moduleSelf => .item scope.id
  | .item selectedItem => .item selectedItem.id
  | .local i => .local i

def unknown (token : Token) (where_ : String := "this scope") : FrenDiag.Diagnostic :=
  ⟨some "F0201", s!"cannot find `{token.text}` in {where_}", token.span⟩

def head (scope : Scope) (ctx : Context) (token : Token) : Except FrenDiag.Diagnostic Selection :=
  if let some index := localIndex ctx token.text then .ok (.local index)
  else if let some item := member scope scope.id token.text then .ok (.item item)
  else if token.text == scope.name.text then .ok .moduleSelf
  else .error (unknown token)

/-- Qualification continues from the selected head. There is deliberately no
retry in an outer scope when a local or non-container item was selected. -/
@[expose] def descend (scope : Scope) (selected : Selection) (token : Token) :
    Except FrenDiag.Diagnostic Selection := do
  let parent ← match selected with
    | .moduleSelf => pure scope.id
    | .item selectedItem =>
      if selectedItem.kind == .enumeration then pure selectedItem.id
      else throw ⟨some "F0204", s!"`{selectedItem.id.render}` has no members", token.span⟩
    | .local _ => throw ⟨some "F0204", "a local variable has no members", token.span⟩
  if let some item := member scope parent token.text then return .item item
  match selected with
  | .item selectedItem => throw ⟨some "F0203", s!"no variant `{token.text}` in enum `{selectedItem.id.render}`", token.span⟩
  | _ => throw (unknown token s!"module `{scope.name.text}`")

def lookup (scope : Scope) (ctx : Context) (path : Path) :
    Except FrenDiag.Diagnostic Selection := do
  let mut selected ← head scope ctx path.head
  for (_, token) in path.tail do
    selected ← descend scope selected token
  return selected

/-- Required categories are checked only in type and pattern positions.
Expression value/callability questions belong to the next pass. -/
def category (scope : Scope) (role : Role) (path : Path) (selected : Selection) :
    Except FrenDiag.Diagnostic Target := do
  if role == .expression then return selected.target scope
  let expected := if role == .annotation then ItemKind.enumeration else .constructor
  if let .item selectedItem := selected then
    if selectedItem.kind == expected then return .item selectedItem.id
  throw ⟨some "F0210", (if role == .annotation then "expected a type" else "expected a variant"), path.head.span⟩

/-- Selecting a local head commits qualification to that local. -/
theorem head_local (scope : Scope) (ctx : Context) (token : Token) (i : Nat)
    (h : localIndex ctx token.text = some i) : head scope ctx token = .ok (.local i) := by
  simp [head, h]

theorem local_no_members (scope : Scope) (i : Nat) (token : Token) :
    descend scope (.local i) token =
      .error ⟨some "F0204", "a local variable has no members", token.span⟩ := rfl

end FrenAstToHir
