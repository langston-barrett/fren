module

import FrenLir

-- Structural laws are proved against the actual production combinators.
example (a b : FrenLir.Lowered) :
    (FrenLir.Lowered.binary .and a b).defined =
      FrenLir.both a.defined b.defined := rfl

example (a b : FrenLir.Lowered) :
    (FrenLir.Lowered.binary .or a b).defined =
      FrenLir.both a.defined b.defined := rfl

example (a b : FrenLir.Lowered) :
    (FrenLir.Lowered.binary .div a b).defined = FrenLir.both
      (FrenLir.both a.defined b.defined) (.binary .ne b.value (.int 0)) := rfl

example (a b : FrenLir.Lowered) :
    (FrenLir.Lowered.binary .iff a b).defined = FrenLir.both a.defined b.defined := rfl

example (binder : FrenAst.Token) (ty : FrenExpr.Ty) (v b : FrenLir.Lowered) :
    (FrenLir.Lowered.bind binder ty v b).verification =
      .both v.verification (.letE binder ty v.value v.defined b.verification) := rfl
