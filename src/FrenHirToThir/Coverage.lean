module

public import FrenHirToThir.Check

public section
namespace FrenHirToThir
open FrenAst FrenModule

/-- Structured failures have no catalogue code until diagnostic rendering is
specified. Missing cases use the match keyword; duplicates use the repeated
pattern's first token. Identity arrays retain declaration/written order. -/
inductive WalkingFailure where
  | coverage (span : FrenSource.Span) (owner : FrenBase.ItemId)
      (missing repeated : Array FrenBase.ItemId)
  | invalidMetadata (span : FrenSource.Span)
  | cycle (span : FrenSource.Span) (functions : Array FrenBase.ItemId)
  deriving Repr, BEq

abbrev ValidationResult := Except WalkingFailure Unit

/-- Helpers consume genuine `check r = .ok t` output. In particular the scope
and occurrence inventory must be complete producer data. They are not an
admission boundary for caller-edited Typed records. The body must belong to
that output and e must be one of its actual written expressions; complete
token sequences distinguish parents from children sharing an anchor. -/
def occurrenceType (body : TypedBody) (e : Expr) : Option ExpressionType :=
  (body.occurrences.find? fun o => o.expression.tokens == e.tokens).map (·.type)

/-- For genuine successful check output, use the actual collected constructor
declarations in source order, filtered by canonical owner. No display-name
matching or hash order. -/
def constructors (t : Typed) (owner : FrenBase.ItemId) : Array FrenBase.ItemId :=
  t.resolved.scope.items.filterMap fun item =>
    if item.kind == .constructor && item.id.parent == some owner then some item.id else none

/-- Requires genuine successful check output. Check every retained match
occurrence, including nested scrutinees and unreachable written arms in
functions, assumptions and expectations. Current AST patterns are constructor
paths only: there is no wildcard/binder case. -/
def validateCoverage (t : Typed) : ValidationResult := do
  for body in t.bodies do
    for occurrence in body.occurrences do
      if let .matchE keyword scrutinee _ arms _ := occurrence.expression then
        let some (.value (.enum owner)) := occurrenceType body scrutinee
          | throw (.invalidMetadata keyword.span)
        let inventory := constructors t owner
        let mut seen := #[]
        let mut repeated := #[]
        let mut repeatedSpan := none
        for (path, _, _, _) in arms do
          let some ref := t.resolved.referenceAt path.head.slice
            | throw (.invalidMetadata path.head.span)
          let .item id := ref.target | throw (.invalidMetadata path.head.span)
          unless ref.role == .pattern && inventory.contains id do
            throw (.invalidMetadata path.head.span)
          if seen.contains id then
            repeated := repeated.push id
            if repeatedSpan.isNone then repeatedSpan := some path.head.span
          seen := seen.push id
        let missing := inventory.filter (!seen.contains ·)
        unless missing.isEmpty && repeated.isEmpty do
          throw (.coverage (repeatedSpan.getD keyword.span) owner missing repeated)
  return ()

@[expose] def WalkingCoverage (t : Typed) : Prop := validateCoverage t = .ok ()

end FrenHirToThir
