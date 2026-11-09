module

public import FrenOirToSmtTests.Cases
public import FrenOirToSmtTests.Model
public import FrenOirToSmtTests.Checker
public import FrenOirToSmtTests.Ownership

public section
namespace FrenOirToSmtTests
open FrenOirToSmt

private def isError : Outcome → Bool
  | .error _ => true | _ => false
private def isResource : Outcome → Bool
  | .resourceExhausted _ => true | _ => false

def runControls : IO Unit := do
  let fd ← Process.testOpenFd
  try
    for piped in [false, true] do
      let command := #["/bin/sh", "-c", s!"test ! -e /proc/self/fd/{fd}"]
      if piped then
        let child ← Process.spawnPiped command true
        Process.closeFd child.stdin
        Process.closeFd child.stdout
        Process.closeFd child.stderr
        require ((← Process.reap child.pid) == .exited 0) "spawn leaked descriptor with pipes"
      else
        let pid ← Process.spawnInherit command true
        require ((← Process.reap pid) == .exited 0) "spawn leaked descriptor without pipes"
  finally
    Process.closeFd fd
  for (bytes, expected) in [
      (#[0xE2, 0x82], "�"), (#[0xE2, 0x82, 0x41], "�A"),
      (#[0xF0, 0x90, 0x80, 0x41], "�A"), (#[0xE0, 0x80, 0x80], "���"),
      (#[0xC2, 0xA2, 0xFF], "¢�")] do
    require (lossyUtf8 (ByteArray.mk bytes) == expected) s!"UTF-8 replacement: {bytes}"
  runCheckerOutcomes
  runCheckerEntryControls
  runModelReadback
  runSourceConfirmation
  let started ← IO.monoMsNow
  let control (mode : String) (limits : Limits := {}) : IO Receipt := do
    let r ← transport (← fakeSolver mode) "(check-sat)\n" limits
    evidence ("control-" ++ mode) (receiptJson r)
    return r
  let unknown ← control "unknown"
  require (unknown.outcome == .unknown "cvc5 returned unknown under the configured limits") "unknown lost"
  require ((← control "unsupported").outcome == .unsupported "cvc5 reported unsupported") "unsupported lost"
  let nonzero ← control "nonzero"
  require (isError nonzero.outcome && nonzero.exitCode == some 7 && nonzero.stdout == "unsat\n" &&
    nonzero.stderr == "owned failure\n") "nonzero exit/stderr was ignored"
  let invalidBytes ← control "bytes"
  require (isError invalidBytes.outcome && invalidBytes.stdoutHex == "ff") "invalid bytes not retained"
  let realUnknown ← ask "(set-logic ALL)\n(declare-const x Int)\n(assert (= (* x x) 2))\n(check-sat)\n"
    {solverResources := 1}
  require (realUnknown.outcome == .unknown "cvc5 returned unknown under the configured limits")
    "real bounded cvc5 unknown was collapsed"
  for mode in ["protocol", "stderr"] do
    require (isError (← control mode).outcome) s!"{mode} became Unsat"
  for mode in ["sleep", "closed", "descendant", "hold-input", "suspended"] do
    let receipt ← control mode {wallMs := 100}
    require (isResource receipt.outcome && receipt.reason == "outer wall deadline") s!"{mode} deadline"
  let flood ← control "flood" {outputBytes := 64}
  require (isResource flood.outcome && flood.stdout.utf8ByteSize + flood.stderr.utf8ByteSize <= 64)
    "unbounded solver output"
  require (isError (← transport #["/nonexistent/fren2-owned-solver"] "").outcome) "missing executable"
  require (isError (← control "unknown" {wallMs := 0}).outcome) "invalid limits"
  require (isResource (← transport #["/bin/false"] "too long" {inputBytes := 1}).outcome) "input limit"
  require (isError (← ask "(set-logic ALL)\n(assert false)\n(check-sat)\n(check-sat)\n").outcome)
    "multiple actual cvc5 answers accepted"
  require (isError (← ask "(set-logic ALL)\n(assert (not))\n(check-sat)\n").outcome)
    "actual cvc5 parse error became a proof"
  for text in #["mod bad\nfn wrong(x: Int): Int := false", "mod bad\nfn loop(x: Int): Int := loop(x)",
      "mod bad\nexpect wrong(x: Int) { expect goal: absent = x }"] do
    require (!(FrenOirToSmt.fromSource ⟨812⟩ text).isOk) "invalid/unsupported walking source admitted"
  let (p, _) ← results "mod test\nexpect check() { expect goal: false }"
  let raw ← validityScript p "check" "goal"
  let flipped := raw.replace "(not false)" "false"
  require (flipped != raw && (← ask raw).outcome == .sat && (← ask flipped).outcome == .unsat)
    "polarity mutation escaped independent false-goal expectation"
  let witness ← load source
  let .ok translated := produce witness | throw (IO.userError "translation witness")
  for (label, oldOp, newOp) in [("negativeDivisor", "(div ", "(mod "),
      ("negativeRemainder", "(mod ", "(div ")] do
    let raw ← validityScript translated "arithmetic" label
    let changed := raw.replace oldOp newOp
    require (changed != raw && (← ask raw).outcome == .unsat && (← ask changed).outcome == .sat)
      s!"signed arithmetic mutant {label}"
  let raw ← validityScript translated "calls" "shadow"
  let changed := raw.replace "(+ L1v 2)" "(+ P0 2)"
  require (changed != raw && (← ask raw).outcome == .unsat && (← ask changed).outcome == .sat)
    "capture/same-type-slot mutant"
  match term 0 translated.oir [] (.bool true) with
  | .error (.resourceExhausted _) => pure ()
  | _ => throw (IO.userError "translation exhaustion vanished")
  let unsupported := {translated.oir with definitions := translated.oir.definitions.reverse}
  -- Stable dependency order must support forward declarations too.
  require ((prelude unsupported).isOk) "declaration order improperly required for definitions"
  let missing := {translated.oir with
    definitions := translated.oir.definitions.filter (fun d => d.signature.id.component != some (.named "later"))}
  match prelude missing with
  | .error (.unsupported _) => pure ()
  | _ => throw (IO.userError "missing function equation silently encoded")
  runOwnership
  IO.println s!"SMT negative controls execution: {(← IO.monoMsNow) - started} ms; actual cvc5 malformed/multiple-answer cases; owned unknown/nonzero/protocol/stderr/UTF8/wall/output/input/missing/invalid controls; 4 independent polarity/arithmetic/capture mutants; 3 rejected sources"

end FrenOirToSmtTests
