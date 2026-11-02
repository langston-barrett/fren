-- keep-sorted start
import FrenCli.Eval
import Lean.Compiler.IR.CompilerM
-- keep-sorted end

/-! Which parameters of the evaluator the compiled code borrows (`@&`),
read from its IR. Whether an annotation holds depends on the compiler: Lean
drops `@&` from a parameter with a default, and owns a parameter that a
self tail call passes an owned value. `Ex.evalIn` has no defaults, and
`evalResult` keeps its self calls out of tail position where they pass an
owned value; `Pat.bindInto` finds an or-pattern's alternative by its index,
so that the alternative it binds is borrowed too. Owned, each parameter
would be counted at every call, which made testing about 30 % slower
(runtime round 11), so a compiler that undid them fails this check, and
the build. -/

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

-- `Pat.bindInto`'s pattern and value borrowed, and its frame owned, which
-- the binding it makes takes over; likewise its payload's.
#eval show CoreM Unit from do
  let bs ← borrows ``FrenCli.Eval.Pat.bindInto
  unless bs == #[true, true, false] do
    throwError "`Pat.bindInto` borrows {bs}, not its pattern and value"
  let bs ← borrows ``FrenCli.Eval.Pat.bindInto.payload
  unless bs == #[true, true, false, false] do
    throwError "`Pat.bindInto.payload` borrows {bs}, not its patterns and values"

end Fren.Test.Borrowing
