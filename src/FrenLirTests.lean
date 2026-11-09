module

import FrenLir

-- Structural laws are proved against the actual production combinators.
example (a b : FrenLir.Lowered) :
    (FrenLir.Lowered.binary .and a b).defined =
      FrenLir.both a.defined (.ite a.value b.defined (.bool true)) := rfl

example (a b : FrenLir.Lowered) :
    (FrenLir.Lowered.binary .or a b).defined =
      FrenLir.both a.defined (.ite a.value (.bool true) b.defined) := rfl

example (a b : FrenLir.Lowered) :
    (FrenLir.Lowered.binary .div a b).defined = FrenLir.both
      (FrenLir.both a.defined b.defined) (.binary .ne b.value (.int 0)) := rfl

example (a b : FrenLir.Lowered) :
    (FrenLir.Lowered.binary .iff a b).defined = FrenLir.both a.defined b.defined := rfl
