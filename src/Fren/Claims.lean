-- keep-sorted start
import Fren.Elab
import FrenCore.Trace
-- keep-sorted end

/-!
# `tested` and `trusted` claims (`Reqs/Trace`)

Fren items, accepted by both front ends; the checks are shared
(`FrenCore.Trace`). They need no solver, so they are part of `Fren.Spec`.
-/

open Lean Elab Command

namespace Fren

namespace Lang

/-- `tested c: "file", ...`: the files are tests that exercise procedure `c`.
A trailing comma is allowed, so that a claim split over several lines
changes by one line when a file is added. -/
scoped syntax (name := testedCmd) "tested " fren_path " : " sepBy1(str, ", ", ", ", allowTrailingSep) : command

/-- `trusted c: "justification"`: why procedure `c` holds without a proof or
a test. -/
scoped syntax (name := trustedCmd) "trusted " fren_path " : " str : command

end Lang

/-- Resolves the procedure of a claim. -/
def resolveComp (p : Syntax) : CommandElabM Name := do
  let r ← resolvePath (← getLocal).currentModule (pathSegs p)
  let .item { kind := .compItem, path, .. } := r | throwErrorAt p (Core.notACompMsg r).text
  return path

@[command_elab Lang.testedCmd] def elabTested : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  lintItem stx
  let path ← resolveComp stx[1]
  let mut files := #[]
  let mut ok := true
  for f in stx[3].getSepArgs do
    let some file := f.isStrLit? | throwUnsupportedSyntax
    let src? ← match ← (IO.FS.readFile file).toBaseIO with
      | .ok src => pure (some src)
      | .error _ => pure none
    if let .error msg := Core.checkTestedFile (Core.showComp path) file src? then
      logErrorAt f msg.text
      ok := false
    files := files.push file
  if ok then record (.claimInfo { comp := path, tested := true, texts := files })

@[command_elab Lang.trustedCmd] def elabTrusted : CommandElab := recordingErrors fun stx => do
  checkLexemes stx
  lintItem stx
  let path ← resolveComp stx[1]
  let some why := stx[3].isStrLit? | throwUnsupportedSyntax
  liftMsg stx[3] (Core.checkTrusted why)
  record (.claimInfo { comp := path, tested := false, texts := #[why] })

end Fren
