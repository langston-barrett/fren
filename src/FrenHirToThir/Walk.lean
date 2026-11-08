module

public import FrenHirToThir.Signature

public section
namespace FrenHirToThir
open FrenAst FrenModule FrenExpr

structure Inferred where
  type : ExpressionType
  occurrences : Array TypedOccurrence
  deriving Repr, BEq

def Inferred.value (result : Inferred) (span : FrenSource.Span) : Result FrenExpr.Ty :=
  match result.type with
  | .value ty => .ok ty
  | .callable _ => .error (failure span "function is not a value")

/-- Every recursive edge consumes one depth unit. The public body entry uses
its actual terminal count plus one, as the resolver does. Exhaustion is a
failure, never a successful truncated traversal. Siblings keep the same ctx. -/
def infer : Nat → Resolved → Array Signature → TypeContext → Expr → Bool → Result Inferred
  | 0, input, _, _, e, _ =>
    .error (failure (anchor e input.scope.name).span "expression depth exhausted")
  | fuel + 1, input, sigs, ctx, e, callable => do
    let span := (anchor e input.scope.name).span
    let finish (ty : ExpressionType) (children : Array TypedOccurrence := #[]) : Inferred :=
      ⟨ty, children.push ⟨e, ctx, ty⟩⟩
    let visit := fun c child => infer fuel input sigs c child false
    let getValue := fun (r : Inferred) (child : Expr) => r.value (anchor child input.scope.name).span
    match e with
    | .bool _ _ => return finish (.value .bool)
    | .integer _ _ => return finish (.value .int)
    | .name path =>
      let ref ← reference input path.head .expression
      unless ref.context == ctx.map Prod.fst do
        throw (failure span "resolved and typed contexts differ")
      match ref.target with
      | .local i =>
        let some ty := localType ctx i | throw (failure span "missing local type")
        return finish (.value ty)
      | .item id =>
        if callable then
          if let some sig := signatureAt sigs id then return finish (.callable sig)
        let some ty := constructorType input id
          | throw (failure span "item is not a value or callable function")
        return finish (.value ty)
      | _ => throw (failure span "type is not an expression value")
    | .paren _ body _ =>
      let result ← infer fuel input sigs ctx body callable
      return finish result.type result.occurrences
    | .unary _ op body =>
      let result ← visit ctx body
      let ty ← getValue result body
      let some out := unary op ty | do
        requireType (anchor body input.scope.name).span (unaryOperand op) ty
        throw (failure span "invalid unary operands")
      return finish (.value out) result.occurrences
    | .binary left _ op right =>
      let l ← visit ctx left
      let lt ← getValue l left
      requireType (anchor left input.scope.name).span (binaryOperand op lt) lt
      let r ← visit ctx right
      let rt ← getValue r right
      let some out := binary op lt rt | do
        requireType (anchor right input.scope.name).span (binaryOperand op lt) rt
        throw (failure span "invalid binary operands")
      return finish (.value out) (l.occurrences ++ r.occurrences)
    | .call callee _ args _ _ =>
      let c ← infer fuel input sigs ctx callee true
      let .callable sig := c.type | throw (failure span "callee is not a function")
      unless args.size == sig.parameters.size do
        throw (failure span s!"expected {sig.parameters.size} arguments, found {args.size}")
      let mut nodes := c.occurrences
      for i in [:args.size] do
        let some arg := args[i]? | throw (failure span "missing argument")
        let r ← visit ctx arg
        let ty ← getValue r arg
        let some param := sig.parameters[i]? | throw (failure span "missing signature parameter")
        requireType (anchor arg input.scope.name).span param.type ty
        nodes := nodes ++ r.occurrences
      return finish (.value sig.result) nodes
    | .ifE _ condition _ yes _ no =>
      let c ← visit ctx condition
      requireType (anchor condition input.scope.name).span .bool (← getValue c condition)
      let y ← visit ctx yes
      let yt ← getValue y yes
      let n ← visit ctx no
      requireType (anchor no input.scope.name).span yt (← getValue n no)
      return finish (.value yt) (c.occurrences ++ y.occurrences ++ n.occurrences)
    | .letE _ name _ value _ body =>
      let v ← visit ctx value
      let vt ← getValue v value
      suffix name vt
      let b ← visit ((name, vt) :: ctx) body
      return finish (.value (← getValue b body)) (v.occurrences ++ b.occurrences)
    | .matchE _ scrutinee _ arms _ =>
      let s ← visit ctx scrutinee
      let st ← getValue s scrutinee
      let .enum _ := st | throw (failure (anchor scrutinee input.scope.name).span "match requires an enum")
      let mut common : Option FrenExpr.Ty := none
      let mut nodes := s.occurrences
      for (path, _, body, _) in arms do
        let ref ← reference input path.head .pattern
        unless ref.context == ctx.map Prod.fst do throw (failure path.head.span "pattern context differs")
        let .item id := ref.target | throw (failure path.head.span "pattern is not a constructor")
        let some pt := constructorType input id | throw (failure path.head.span "pattern is not a constructor")
        requireType path.head.span st pt
        let b ← visit ctx body
        let bt ← getValue b body
        if let some expected := common then requireType (anchor body input.scope.name).span expected bt
        else common := some bt
        nodes := nodes ++ b.occurrences
      let some out := common | throw (failure span "cannot infer an empty match result")
      return finish (.value out) nodes

end FrenHirToThir
