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

/-- The coverage inventory of one match: the owner's constructors that no arm
targets, in inventory order, and each arm target that an earlier arm already
targeted, in written order. A match covers its owner exactly when both are
empty, so that every constructor has exactly one arm. Generic in the item
type so that the specification binds this function itself. -/
@[expose] def coverage {α : Type} [BEq α] (inventory targets : Array α) : Array α × Array α :=
  let missing := inventory.filter fun c => !targets.contains c
  let repeated := (targets.foldl (init := ((#[] : Array α), (#[] : Array α)))
    fun (seen, repeated) t =>
      (seen.push t, if seen.contains t then repeated.push t else repeated)).2
  (missing, repeated)

/-- The arm of a match that a constructor selects: the first arm, in written
order, whose target is that constructor. Generic in the arm and item types so
that the specification binds this function itself; the evaluator and the
confirmation of a strict evaluation both select through it. -/
@[expose] def selectArm {α β : Type} [BEq α] (arms : Array β) (target : β → Option α)
    (constructor : α) : Option β :=
  arms.find? fun arm => target arm == some constructor

/-- The constructor that a written pattern resolves to, when it is a pattern
reference to an item. -/
def patternConstructor (resolved : FrenModule.Resolved) (path : FrenAst.Path) :
    Option FrenBase.ItemId :=
  resolved.referenceAt path.head.slice |>.bind fun ref =>
    match ref.target with
    | .item id => if ref.role == .pattern then some id else none
    | _ => none

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
        let mut targets := #[]
        for (path, _, _, _) in arms do
          let some ref := t.resolved.referenceAt path.head.slice
            | throw (.invalidMetadata path.head.span)
          let .item id := ref.target | throw (.invalidMetadata path.head.span)
          unless ref.role == .pattern && inventory.contains id do
            throw (.invalidMetadata path.head.span)
          targets := targets.push id
        let (missing, repeated) := coverage inventory targets
        unless missing.isEmpty && repeated.isEmpty do
          -- The first repeated arm is the second arm for the first repeated target.
          let span := repeated[0]?.bind fun r =>
            let second := (arms.toList.filter fun (path, _, _, _) =>
              patternConstructor t.resolved path == some r)[1]?
            second.map fun (path, _, _, _) => path.head.span
          throw (.coverage (span.getD keyword.span) owner missing repeated)
  return ()

@[expose] def WalkingCoverage (t : Typed) : Prop := validateCoverage t = .ok ()

end FrenHirToThir
