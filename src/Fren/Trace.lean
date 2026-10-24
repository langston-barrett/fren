-- keep-sorted start
import Fren.Claims
import Fren.Impl
-- keep-sorted end

/-!
# `#fren_trace` (`Reqs/Trace`)

Reports the evidence for every component: its `impl`s and claims, or, for a
component without outputs, its instances'. The logic and text are shared
with `fren trace` (`FrenCore.Trace`).
-/

open Lean Elab Command

namespace Fren

namespace Lang

/-- Reports the evidence for every component (`trace::required`). -/
scoped syntax (name := traceCmd) "#fren_trace" : command

end Lang

register_option fren.requireEvidence : String := {
  defValue := ""
  descr := "make `#fren_trace` warn about components with weaker evidence than this: \
    \"trusted\", \"tested\", \"solver\" or \"proved\""
}

register_option fren.testGlobs : String := {
  defValue := ""
  descr := "space-separated globs of test files that `#fren_trace` scans for `fren-covers:` markers"
}

@[command_elab Lang.traceCmd] def elabTrace : CommandElab := fun _ => do
  let s ← getState
  let opt := fren.requireEvidence.get (← getOptions)
  let threshold ← if opt.isEmpty then pure Core.Level.missing else
    match Core.Level.ofName? opt with
    | some l => pure l
    | none => throwError (Core.unknownLevelMsg opt).text
  let claims : Core.Claims := { tested := s.tested, trusted := s.trusted }
  let comps := s.comps.toList.map (·.2) |>.toArray.qsort (·.path.toString < ·.path.toString)
  let traceComps := comps.map fun c =>
    let impls := s.impls.getD c.path #[]
    { path := c.path, hasOutputs := c.vars.any (·.role == .output), insts := c.insts.map (·.comp)
      proved := impls.any (!s.axiomImpls.contains ·), solver := impls.any s.axiomImpls.contains : Core.TraceComp }
  let ls := Core.levels traceComps claims
  let paths := comps.map (·.path)
  for p in paths do
    let l := ls.getD p .missing
    if let some .warning := Core.traceSeverity l threshold !opt.isEmpty then
      logWarning (Core.belowMsg p l threshold "`fren.requireEvidence`").text
  -- The converse of `tested` claims, over the scanned tests
  let globs := (fren.testGlobs.get (← getOptions)).splitOn " " |>.filter (!·.isEmpty) |>.toArray
  unless globs.isEmpty do
    let files ← Core.expandGlobs globs
    let srcs ← files.filterMapM fun (f : String) => do
      match ← (IO.FS.readFile (System.FilePath.mk f)).toBaseIO with
      | .ok src => pure (some (f, src))
      | .error _ => pure none
    for st in Core.strays paths claims srcs do
      logError s!"{st.file}:{st.line}: {st.msg.text}"
  logInfo (Core.traceSummary paths ls)

end Fren
