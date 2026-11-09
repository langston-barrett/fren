module

public import FrenHirToThir
meta import FrenHirToThir

/-! Hand-written HIR inputs for the separated pass, for the errors the
generator does not inject: a local callee, an unwritten type without the `?`
suffix, an enum name as a value or callee, a function name as a pattern, and a
non-enum scrutinee with arms; plus a few accepted and arm-agreement cases. -/

namespace FrenHirToThirTests.PassCases
open FrenExpr FrenModule.Core FrenHirToThir.Pass

private def m : FrenBase.ItemId := FrenBase.ItemId.root.named "m"
private def E : FrenBase.ItemId := m.named "E"
private def A : FrenBase.ItemId := E.named "A"
private def f : FrenBase.ItemId := m.named "f"
private theorem g : Phase.Untyped .hir := rfl

private def h (o : OriginId) (n : ExprF .hir (Expr .hir)) : Expr .hir := ⟨o, (), n⟩

/-- `enum E { A }` and `fn f(x: Int): Int := body`. -/
private def module (body : Expr .hir) (param : Param := ⟨1, .int, false, true⟩) : Hir :=
  ⟨m, #[.enum ⟨E, 0, #[A]⟩ #[{}],
        .function ⟨f, 0, #[param], .int, body⟩ (Array.replicate 8 {})]⟩

private def rejects (body : Expr .hir) (o : OriginId) (r : Reason) : Bool :=
  match typeModule (module body) with
  | .error e => e == ⟨f, o, r⟩
  | .ok _ => false

-- Accepted: a call of `f`, with a constructor compared inside.
private def same : Expr .hir := h 4 (.binary .eq (h 5 (.item g A)) (h 6 (.item g A)))
#guard (typeModule (module (h 2 (.apply g (.item f) #[h 3 (.ite same (h 7 (.var 0)) (h 8 (.int 0)))])))).isOk

-- A local is never callable, even of the right arity.
#guard rejects (h 2 (.apply g (.local 0) #[h 3 (.int 1)])) 2 (.notCallable (.local 0))
-- An enum name and a function name are not values.
#guard rejects (h 2 (.item g E)) 2 (.notValue E)
#guard rejects (h 2 (.binary .add (h 3 (.item g f)) (h 4 (.int 1)))) 3 (.notValue f)
-- An enum's own name is not a callee; a function is not a pattern.
#guard rejects (h 2 (.apply g (.item E) #[h 3 (.int 1)])) 2 (.notCallable (.item E))
#guard rejects (h 2 (.matchE (h 3 (.item g A)) #[(⟨4, f⟩, h 5 (.int 0))])) 4 (.patternNotConstructor f)
-- Later arms must have the first arm's type.
#guard rejects (h 2 (.matchE (h 3 (.item g A)) #[(⟨4, A⟩, h 5 (.int 0)), (⟨6, A⟩, h 7 (.bool true))]))
  7 (.mismatch .int .bool)
-- A match on a non-enum is rejected at the scrutinee, before any arm.
#guard rejects (h 2 (.matchE (h 3 (.var 0)) #[(⟨4, f⟩, h 5 (.int 0))])) 3 (.matchNotEnum .int)
-- An unwritten type needs the `?` suffix; the suffix needs `Bool`.
#guard match typeModule (module (h 2 (.int 0)) ⟨1, .bool, false, false⟩) with
  | .error e => e == ⟨f, 1, .missingAnnotation⟩ | .ok _ => false
#guard (typeModule (module (h 2 (.int 0)) ⟨1, .bool, true, false⟩)).isOk
-- A let's binder is in scope in its body only, and is the nearest local there.
private def letBody : Expr .hir := h 5 (.ite (h 6 (.var 0)) (h 7 (.var 1)) (h 8 (.int 0)))
#guard (typeModule (module (h 2 (.letE ⟨3, true⟩ (h 4 (.bool true)) letBody)))).isOk
#guard rejects (h 2 (.letE ⟨3, false⟩ (h 4 (.var 1)) (h 5 (.int 0)))) 4 (.danglingLocal 1)
-- Type errors carry spans only through the origin table: none here.
#guard match typeModule (module (h 2 (.bool true))) with
  | .error e => e.diagnostic (module (h 2 (.bool true))) == none && e.code == some "F0304"
  | .ok _ => false

end FrenHirToThirTests.PassCases
