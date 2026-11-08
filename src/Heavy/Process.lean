import Std

/-! Pure conversion of raw Linux process observations. The standalone launcher
uses these functions; the requirements import this module, never conversely. -/

namespace Heavy.Process

structure Result where
  kind : Nat
  detail : Nat
  shellCode : Nat
  deriving Repr, BEq

/-- Kinds: ordinary exit, signal, exec failure, observer failure. -/
def result (launchError execError waitError status : Nat) : Result :=
  if launchError > 0 then ⟨3, launchError, 125⟩
  else if waitError > 0 then ⟨3, waitError, 125⟩
  else if execError > 0 then ⟨2, execError, 127⟩
  else if status % 128 = 0 then ⟨0, status / 256 % 256, status / 256 % 256⟩
  else if status % 128 < 127 then ⟨1, status % 128, 128 + status % 128⟩
  else ⟨3, 0, 125⟩

def elapsed (clockError start finish : Nat) : Option Nat :=
  if clockError = 0 ∧ finish ≥ start then some (finish - start) else none

/-- Raw wait4 usage is present only for an executed, reaped, terminated child.
Signals retain measured usage, but do not establish demand to completion. -/
def usage (launchError execError waitError status user system rss : Nat) : Option (Nat × Nat) :=
  if launchError = 0 ∧ execError = 0 ∧ waitError = 0 ∧ status % 128 < 127 then
    some (user + system, rss) else none

/-- Linux raw mode and size, inspected on the opened descriptor. A bounded
regular-file read cannot consume a FIFO or allocate an unbounded buffer. -/
def fingerprintAllowed (mode bytes : Nat) : Bool :=
  decide (mode / 4096 % 16 = 8 ∧ bytes ≤ 67108864)

/-- Metadata stops after the operand of --run; program arguments are opaque.
The actual compiler invocation retains the entire original argument list. -/
def compilerArguments : List String → List String
  | [] => []
  | arg :: rest => if arg == "--run" then arg :: rest.take 1
      else arg :: compilerArguments rest

def identityPart : Option String → Bool
  | some s => s != ""
  | none => false

/-- A fingerprint of source bytes alone is deliberately insufficient. The
caller must leave the input closure absent when it cannot observe it. -/
def identityComplete (source toolchain inputClosure : Option String) : Bool :=
  identityPart source && identityPart toolchain && identityPart inputClosure

end Heavy.Process
