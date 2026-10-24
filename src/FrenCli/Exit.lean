-- keep-sorted start
import FrenCore.Check
-- keep-sorted end

/-! # The binary's exit code (`cli::exit`) -/

namespace FrenCli

/-- The exit code, given whether the checks ran and the most severe result
(`none` if every check passed). -/
def exitCode (ran : Bool) (worst : Option Fren.Core.Severity) : UInt32 :=
  if !ran then 2
  else match worst with
    | some .error => 1
    | some .warning => 3
    | _ => 0

end FrenCli
