module

public import FrenOirToSmt.Types
public import Lean.Data.Json

public section
namespace FrenOirToSmt
open Lean

/-- Exit and complete protocol are checked before recognizing an answer. A
solver diagnostic, extra answer or nonzero exit can never become Unsat. -/
@[expose] def classify (exitCode : Option Int) (stdout stderr kind reason : String) : Outcome :=
  if kind == "resource" then .resourceExhausted reason
  else if kind != "finished" then .error reason
  else if exitCode != some 0 then .error "solver exited unsuccessfully"
  else if !stderr.trimAscii.toString.isEmpty then .error "solver stderr diagnostic"
  else match stdout.trimAscii.toString with
    | "sat" => .sat
    | "unsat" => .unsat
    | "unsupported" => .unsupported "cvc5 reported unsupported"
    | "unknown" => .unknown "cvc5 returned unknown under the configured limits"
    | _ => .error "invalid solver answer protocol"

/-- Paths belong to the source tree shipped with the Lake executable. Missing
assets are explicit transport errors; this code never downloads a solver. -/
def sourceRoot : IO System.FilePath := do
  let app ← IO.appPath
  let some dir := app.parent | throw (IO.userError "no executable directory")
  IO.FS.realPath (dir / ".." / ".." / "..")

def solverCommand (limits : Limits) : IO (Array String) := do
  let root ← sourceRoot
  return #[(root / ".lake/packages/cvc5/cvc5-Linux-x86_64-static/bin/cvc5").toString,
    "--lang=smt2", s!"--tlimit-per={limits.solverMs}", s!"--rlimit-per={limits.solverResources}"]

private def decode (raw request binding : String) (limits : Limits) : Except String Receipt := do
  let j ← Json.parse raw
  let command ← j.getObjValAs? (Array String) "command"
  let exitCode ← j.getObjValAs? (Option Int) "exit_code"
  let stdout ← j.getObjValAs? String "stdout"
  let stderr ← j.getObjValAs? String "stderr"
  let stdoutHex ← j.getObjValAs? String "stdout_hex"
  let stderrHex ← j.getObjValAs? String "stderr_hex"
  let elapsed ← j.getObjValAs? Nat "elapsed_ms"
  let kind ← j.getObjValAs? String "kind"
  let reason ← j.getObjValAs? String "reason"
  return ⟨command, exitCode, stdout, stderr, stdoutHex, stderrHex, elapsed, reason, classify exitCode stdout stderr kind reason, request, binding, kind, limits⟩

/-- Low-level transport is exposed for owned failure controls. The source
producer/solver entry never accepts its output as an admission witness. -/
def transport (command : Array String) (script : String) (limits : Limits := {}) (binding : String := "") : IO Receipt := do
  let started ← IO.monoMsNow
  let failure (message : String) : IO Receipt := do
    return ⟨command, none, "", "", "", "", (← IO.monoMsNow) - started, message, .error message, script, binding, "error", limits⟩
  if limits.wallMs == 0 || limits.wallMs > 10000 || limits.solverMs == 0 ||
      limits.solverResources == 0 || limits.outputBytes == 0 || limits.outputBytes > 1048576 ||
      limits.inputBytes == 0 || limits.inputBytes > 1048576 then
    return ← failure "invalid bounded solver limits"
  if script.utf8ByteSize > limits.inputBytes then
    return ⟨command, none, "", "", "", "", 0, "script input limit", .resourceExhausted "script input limit", script, binding, "resource", limits⟩
  try
    let root ← sourceRoot
    let request := Json.mkObj [("command", toJson command), ("script", toJson script),
      ("wall_ms", toJson limits.wallMs), ("output_bytes", toJson limits.outputBytes),
      ("input_bytes", toJson limits.inputBytes)]
    let out ← IO.Process.output {cmd := "python3", args := #[(root / "src/FrenOirToSmt/transport.py").toString]}
      (some request.compress)
    if out.exitCode != 0 then return ← failure s!"transport helper exit {out.exitCode}: {out.stderr}"
    match decode out.stdout script binding limits with
    | .ok receipt => return receipt
    | .error e => return ← failure ("transport helper protocol: " ++ e)
  catch e => failure ("transport setup: " ++ e.toString)

theorem classify_nonzero (code : Int) (h : code ≠ 0) :
    classify (some code) "unsat" "" "finished" "" = .error "solver exited unsuccessfully" := by
  simp [classify, h]

theorem classify_resource (code : Option Int) (out err reason : String) :
    classify code out err "resource" reason = .resourceExhausted reason := rfl

end FrenOirToSmt
