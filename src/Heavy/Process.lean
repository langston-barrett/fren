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

/-- Observed child peak above a positive requested reservation, in KiB.
Absent inputs and a zero request carry no comparison. -/
def requestExcess (requested observed : Option Nat) : Option Nat := do
  let request ← requested
  let peak ← observed
  if request = 0 then none else some (peak - request)

theorem requestExcess_positive (request peak : Nat) (h : request > 0) :
    requestExcess (some request) (some peak) = some (peak - request) := by
  simp [requestExcess, Nat.ne_of_gt h]

theorem requestExcess_zero_of_le (request peak : Nat) (h : peak ≤ request) :
    requestExcess (some request) (some peak) = if request = 0 then none else some 0 := by
  simp [requestExcess, Nat.sub_eq_zero_of_le h]

/-- Linux raw mode/size from an O_PATH descriptor, before read-capable open.
This decides eligibility, not whether acquiring identity has OS side effects. -/
def fingerprintAllowed (mode bytes : Nat) : Bool :=
  decide (mode / 4096 % 16 = 8 ∧ bytes ≤ 67108864)

/-- A conservative selected-input/requested-output description, not a claim
that failed compilation consumed/produced bytes. `none` means unsupported. -/
structure Metadata where
  kind : String
  source : Option String := none
  olean : Option String := none
  ilean : Option String := none
  c : Option String := none
  bc : Option String := none
  setup : Option String := none
  deriving Repr, BEq

/-- Zero disables the limit; positive values apply only to budgeted non-query
compiler invocations. Values above the native protocol bound are invalid. -/
def compilerCpuLimit (seconds : Nat) (gated query : Bool) : Option Nat :=
  if seconds > 2147483647 then none
  else if seconds > 0 && !gated then none
  else some (if query then 0 else seconds)

/-- The wall setting has the same selection and native range as CPU, in milliseconds. -/
def compilerWallLimit (milliseconds : Nat) (gated query : Bool) : Option Nat :=
  compilerCpuLimit milliseconds gated query

/-- Interpret the actual private pipe observation, not PID or EOF alone. -/
def appliedCompilerCpu (seconds bytes first readError eof waitError : Nat) : Option Nat :=
  if seconds > 0 && (bytes == 4 || bytes == 8) && first == 1212371029 &&
      readError == 0 && eof == 1 && waitError == 0 then some seconds else none

def emptyMetadata (kind : String) : Metadata := ⟨kind, none, none, none, none, none, none⟩

def valueFlag (arg : String) : Bool := decide
  (arg = "-o" ∨ arg = "-i" ∨ arg = "-c" ∨ arg = "-b" ∨ arg = "--setup" ∨
   arg = "-R" ∨ arg = "--root")

def queryFlag (arg : String) : Bool := decide
  (arg = "--version" ∨ arg = "-v" ∨ arg = "--short-version" ∨ arg = "-V" ∨
   arg = "--githash" ∨ arg = "-g" ∨ arg = "--help" ∨ arg = "-h" ∨
   arg = "--features" ∨ arg = "--print-prefix" ∨ arg = "--print-libdir")

def plainFlag (arg : String) : Bool := decide
  (arg = "--json" ∨ arg = "-q" ∨ arg = "--stats" ∨
   arg = "-Dweak.fren.runChecks=false")

def optionLike (arg : String) : Bool := ['-'].isPrefixOf arg.toList

def setMetadata (m : Metadata) (flag value : String) : Metadata :=
  { kind := if flag = "--stdin" then "stdin" else m.kind
    source := if flag = "input" then some value else m.source
    olean := if flag = "-o" then some value else m.olean
    ilean := if flag = "-i" then some value else m.ilean
    c := if flag = "-c" then some value else m.c
    bc := if flag = "-b" then some value else m.bc
    setup := if flag = "--setup" then some value else m.setup }

def finishMetadata (m : Metadata) : Option Metadata :=
  if m.kind = "stdin" then some {m with source := none}
  else match m.source with | some _ => some m | none => none

/-- Consume operands before interpreting flags. Unsupported syntax discards
all affected metadata instead of guessing; forwarding does not use this result. -/
def metadataLoop : List String → Metadata → Option Metadata
  | [], m => finishMetadata m
  | arg :: rest, m =>
    if valueFlag arg then match rest with
      | [] => none
      | value :: tail => metadataLoop tail (setMetadata m arg value)
    else if queryFlag arg then some (emptyMetadata "query")
    else if arg = "--stdin" then metadataLoop rest (setMetadata m arg "")
    else if arg = "--run" then match rest, m.source with
      | file :: _, none => if optionLike file then none else finishMetadata (setMetadata m "input" file)
      | _, _ => none
    else if plainFlag arg then metadataLoop rest m
    else if optionLike arg then none
    else match m.source with
      | some _ => none
      | none => metadataLoop rest (setMetadata m "input" arg)

def parseMetadata (args : List String) : Option Metadata := metadataLoop args (emptyMetadata "file")

def identityPart : Option String → Bool
  | some s => s != ""
  | none => false

/-- Raw observations from the current compiler and trusted immutable setup.
Checksums detect damage; query stability is the native Lean caller contract. -/
def reuseMetadata (currentPath : String) (currentFingerprint : Option String)
    (preparedPath preparedFingerprint version githash : String)
    (observedChecksum storedChecksum : Nat) : Bool :=
  decide (currentPath ≠ "" ∧ currentPath = preparedPath ∧
    currentFingerprint = some preparedFingerprint ∧ preparedFingerprint ≠ "" ∧
    version ≠ "" ∧ githash ≠ "" ∧ observedChecksum = storedChecksum)

/-- A fingerprint of source bytes alone is deliberately insufficient. The
caller must leave the input closure absent when it cannot observe it. -/
def identityComplete (source toolchain inputClosure : Option String) : Bool :=
  identityPart source && identityPart toolchain && identityPart inputClosure

end Heavy.Process
