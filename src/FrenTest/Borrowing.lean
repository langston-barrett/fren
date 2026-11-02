-- keep-sorted start
import FrenCli.Eval
import Lean.Compiler.IR.CompilerM
-- keep-sorted end

/-! Which parameters of the evaluator the compiled code borrows (`@&`),
read from its IR. Whether an annotation holds depends on the compiler: Lean
drops `@&` from a parameter with a default, and owns a parameter that a
self tail call passes an owned value, or that is passed to a function that
takes it over. `Ex.evalIn` has no defaults, and `own` and `evalResult`
keep the rest from owning its parameters. Owned, each would be counted at
every call of `Ex.evalIn`, which made testing about 30 % slower (runtime
round 11), so a compiler that undid them fails this check, and the build.
-/

namespace Fren.Test.Borrowing

open Lean

/-- `n`'s parameters, as whether each is borrowed, in its IR. -/
def borrows (n : Name) : CoreM (Array Bool) := do
  let some d := IR.findEnvDecl (← getEnv) n | throwError "{n} has no IR"
  return d.params.map (·.borrow)

-- `I`, `look`, `locals`, `slots`, `frame` and `memos` borrowed, `fuel` and
-- `depth` (`Nat`s) owned, and `e` borrowed.
#eval show CoreM Unit from do
  let bs ← borrows ``FrenCli.Eval.Ex.evalIn
  unless bs == #[true, true, true, true, true, true, false, false, true] do
    throwError "`Ex.evalIn` borrows {bs}, not all of `I`, `look`, `locals`, `slots`, `frame`, `memos` and `e`"

-- `quantV`'s `frame` and `memos`, its last two parameters, borrowed.
#eval show CoreM Unit from do
  let bs ← borrows ``FrenCli.Eval.Ex.evalIn.quantV
  unless bs.size ≥ 2 && bs[bs.size - 2]! && bs[bs.size - 1]! do
    throwError "`Ex.evalIn.quantV` borrows {bs}, not `frame` and `memos`"

end Fren.Test.Borrowing
