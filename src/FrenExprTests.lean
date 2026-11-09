module

public import FrenExpr
meta import FrenExpr

/-! Build-time tests of the expression core: gates, the functor laws on
concrete layers, the fold's equation, scoping, erasure and the printer's
origin-blind equality. -/

namespace FrenExprTests
open FrenExpr

private def e (k : String) : FrenBase.ItemId := (FrenBase.ItemId.root.named "m").named k

private theorem hirUntyped : Phase.Untyped .hir := rfl
private theorem thirTyped : Phase.Typed .thir := by decide
private theorem hirSurface : Phase.Surface .hir := Or.inl rfl

-- Gates: decisions exist only after typing; surface forms only up to THIR.
#guard decide (Phase.Untyped .hir) && !decide (Phase.Untyped .thir)
#guard decide (Phase.Typed .mir) && !decide (Phase.Typed .hir)
#guard decide (Phase.Surface .thir) && !decide (Phase.Surface .dthir) && !decide (Phase.Surface .flat)
example : ¬ Phase.Untyped .thir := by decide
example (g : Phase.Surface .flat) : False := by simp [Phase.Surface] at g

private def h (o : OriginId) (n : ExprF .hir (Expr .hir)) : Expr .hir := ⟨o, (), n⟩
private def t (o : OriginId) (ty : Ty) (n : ExprF .thir (Expr .thir)) : Expr .thir := ⟨o, ty, n⟩

/-- `let x := 1 in (x + p)` under one parameter `p` (index 1 in the body). -/
private def sample : Expr .hir :=
  h 0 (.letE ⟨1, false⟩ (h 2 (.int 1))
    (h 3 (.paren hirSurface (h 4 (.binary .add (h 5 (.var 0)) (h 6 (.var 1)))))))

-- Children are in written order; map is a functor on a concrete layer.
#guard ((ExprF.ite (p := .hir) 1 2 3).children == [1, 2, 3])
#guard ((ExprF.matchE (p := .hir) 0 #[(⟨9, e "A"⟩, 1), (⟨8, e "B"⟩, 2)]).children == [0, 1, 2])
#guard ((ExprF.binary (p := .thir) .add 1 2).map (· * 10)).children == [10, 20]
example (n : ExprF .hir Nat) : n.map id = n := ExprF.map_id n

-- Folds: size counts every node; scoping counts enclosing binders.
#guard sample.size == 6
#guard sample.scopedIn 1 && !sample.scopedIn 0
#guard !(h 0 (.apply hirUntyped (.local 2) #[h 1 (.int 0)])).scopedIn 2
#guard (h 0 (.apply hirUntyped (.local 1) #[h 1 (.int 0)])).scopedIn 2

-- The fold's equation, on a concrete layer.
example (alg : OriginId → Ann .hir → ExprF .hir Nat → Nat) :
    sample.fold alg = alg 0 () ((ExprF.letE ⟨1, false⟩ (h 2 (.int 1)) (h 3 (.paren hirSurface
      (h 4 (.binary .add (h 5 (.var 0)) (h 6 (.var 1))))))).map (Expr.fold alg)) :=
  Expr.fold_mk alg 0 () _

-- Origins are excluded from structural equality, but printed on request.
#guard sample.same (Expr.fold (fun o a n => (⟨o + 100, a, n⟩ : Expr .hir)) sample)
#guard !(sample.toSexp true == (Expr.fold (fun o a n => (⟨o + 100, a, n⟩ : Expr .hir)) sample).toSexp true)
#guard !sample.same (h 0 (.int 1))

-- Erasure forgets types and turns decided forms back into references.
private def typed : Expr .thir :=
  t 0 .int (.call thirTyped (e "f") #[t 1 (.enum (e "E")) (.ctor thirTyped ((e "E").named "A"))])
#guard typed.eraseTypes.same (h 0 (.apply hirUntyped (.item (e "f")) #[h 1 (.item hirUntyped ((e "E").named "A"))]))
#guard typed.eraseTypes.toSexp true == (h 0 (.apply hirUntyped (.item (e "f"))
  #[h 1 (.item hirUntyped ((e "E").named "A"))])).toSexp true
#guard !(typed.toSexp == (t 0 .bool (.call thirTyped (e "f")
  #[t 1 (.enum (e "E")) (.ctor thirTyped ((e "E").named "A"))])).toSexp)

/-- The generic fold theorem in use: a hand-written recursion that satisfies
the fold's equation is the fold, so it inherits every fold law. -/
example (alg : OriginId → Ann .hir → ExprF .hir Nat → Nat) (f : Expr .hir → Nat)
    (eqn : ∀ o a n, f ⟨o, a, n⟩ = alg o a (n.map f)) : f sample = sample.fold alg :=
  Expr.fold_unique alg f eqn sample

end FrenExprTests
