module

public import FrenHirToThir.Check

public section
namespace FrenHirToThir
open FrenAst FrenModule FrenExpr

/-- A selected occurrence in its exact lexical context; this relation does not
perform another lexical or path search. -/
def Selects (r : Resolved) (ctx : TypeContext) (p : Path) (role : Role) (target : Target) : Prop :=
  ∃ ref, r.referenceAt p.head.slice = some ref ∧ ref.role = role ∧ ref.target = target ∧
    ref.context = ctx.map Prod.fst

/-- Declarative typing over the actual retained AST. No executable spec IR
or second traversal is used. Operators use the proved generic primitives. -/
inductive HasValue (r : Resolved) (sigs : Array Signature) : TypeContext → Expr → FrenExpr.Ty → Prop where
  | bool : HasValue r sigs ctx (.bool token value) .bool
  | integer : HasValue r sigs ctx (.integer token value) .int
  | local : Selects r ctx path .expression (.local i) →
      FrenBase.Binding.HasType ctx i (token, ty) → HasValue r sigs ctx (.name path) ty
  | constructor {itemId : FrenBase.ItemId} : Selects r ctx path .expression (.item itemId) →
      constructorType r itemId = some ty → HasValue r sigs ctx (.name path) ty
  | paren : HasValue r sigs ctx body ty → HasValue r sigs ctx (.paren o body c) ty
  | unary : HasValue r sigs ctx body operand → FrenExpr.unary op operand = some ty →
      HasValue r sigs ctx (.unary token op body) ty
  | binary : HasValue r sigs ctx left lt → HasValue r sigs ctx right rt →
      FrenExpr.binary op lt rt = some ty → HasValue r sigs ctx (.binary left token op right) ty
  | call : Selects r ctx path .expression (.item sig.id) → signatureAt sigs sig.id = some sig →
      args.size = sig.parameters.size →
      (∀ i (hi : i < args.size) (hp : i < sig.parameters.size),
        HasValue r sigs ctx args[i] sig.parameters[i].type) →
      HasValue r sigs ctx (.call (.name path) o args commas c) sig.result
  | ifE : HasValue r sigs ctx condition .bool → HasValue r sigs ctx yes ty →
      HasValue r sigs ctx no ty → HasValue r sigs ctx (.ifE i condition t yes e no) ty
  | letE : HasValue r sigs ctx value vt → suffix name vt = .ok () →
      HasValue r sigs ((name, vt) :: ctx) body ty →
      HasValue r sigs ctx (.letE l name assign value i body) ty
  | matchE : HasValue r sigs ctx scrutinee (.enum owner) → arms.isEmpty = false →
      (∀ arm ∈ arms.toList, ∃ itemId,
        Selects r ctx arm.1 .pattern (.item itemId) ∧ constructorType r itemId = some (.enum owner)) →
      (∀ arm ∈ arms.toList, HasValue r sigs ctx arm.2.2.1 ty) →
      HasValue r sigs ctx (.matchE m scrutinee o arms c) ty

end FrenHirToThir
