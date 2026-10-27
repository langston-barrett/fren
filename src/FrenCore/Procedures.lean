-- keep-sorted start
import FrenCore.Diagnostic
-- keep-sorted end

/-!
# Procedures

A procedure (`Reqs/Lang/Procedures`) declares its inputs as parameters and
its public outputs as named results, and its other members in its block.
A call gives an argument for each of the called procedure's parameters,
in order (`call::arguments`).
-/

namespace Fren.Core

/-! ## A call's arguments -/

/-- Whether a call gives each parameter of the called procedure an argument
(`call::Arity`). -/
inductive CallArity where
  | fits
  | tooMany
  | tooFew
  deriving Inhabited, DecidableEq, Repr

/-- Whether a call with `nArgs` arguments gives each of `nParams` parameters
one (`call::arguments`). -/
def callArity (nParams nArgs : Nat) : CallArity :=
  if nArgs == nParams then .fits else if nArgs > nParams then .tooMany else .tooFew

/-- What a call binds, if its arguments fit the called procedure's
parameters `params`: each parameter to the argument in its position
(`call::arguments`). Both front ends and the evaluator bind a call's
arguments so. -/
def callBindings {α : Type} (params : Array String) (args : Array α) : Option (Array (String × α)) :=
  if callArity params.size args.size == .fits then some (params.zip args) else none

/-! ## Messages -/

/-- A parameter declared with the modifier `mod`, `pub` or `det` (`F0110`),
whose fix removes it at `fix?`. -/
def paramModifierMsg (mod : String) (fix? : Option Range := none) : Msg :=
  { code? := some "F0110", headline := s!"parameters cannot be declared `{mod}`"
    label? := some "not allowed on a parameter"
    notes := #["note: a parameter is an input: the environment chooses it, sees it, and determines it"]
    fixes := #[{ msg := s!"remove `{mod}`", replacement := "", range? := fix? }] }

/-- A result defined by more than one `out` member (`F0421`). -/
def resultDefinedTwiceMsg (r : String) : Msg :=
  { code? := some "F0421", headline := s!"result `{r}` is defined more than once"
    label? := some "defined again here"
    notes := #["note: a result is defined by one `out` member at most, or is chosen by the system"] }

/-- A call with `given` arguments, of a procedure with `params`
(`F0408`, `F0409`). -/
def callArityMsg (callee : String) (params : Array String) (given : Nat) : Msg :=
  let n := params.size
  let takes := if n == 0 then "takes no arguments"
    else s!"takes {n} argument{if n == 1 then "" else "s"}, {", ".intercalate (params.toList.map fun p => s!"`{p}`")}"
  if given > n then
    { code? := some "F0408", headline := s!"too many arguments: `{callee}` {takes}"
      label? := some s!"{given} arguments", notes := #["note: a call gives one argument for each parameter, in order"] }
  else
    let missing := params.extract given n
    { code? := some "F0409", headline := s!"too few arguments: `{callee}` {takes}"
      label? := some s!"{given} argument{if given == 1 then "" else "s"}"
      notes := #["note: a call gives one argument for each parameter, in order",
        s!"help: add {", ".intercalate (missing.toList.map fun p => s!"`{p}`")}"] }

end Fren.Core
