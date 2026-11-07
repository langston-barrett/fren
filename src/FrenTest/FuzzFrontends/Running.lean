-- keep-sorted start
import Fren
import FrenCli.Run
import FrenTest.Frontends
import FrenTest.Messages
import Lean.Elab.Frontend
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends

/-! ### Running the front ends -/

open FrenTest.Ui (Diagnostic)
open FrenTest.Frontends (Report maskBetween headOf)

/-- What both front ends said on a spec. -/
structure Ran where
  /-- How they differ. -/
  comparison : FrenTest.Frontends.Comparison
  /-- Both reports, as comments. -/
  reports : String
  /-- The binary's error codes, or headlines for code-less errors, without
  the stopped trailer (`errorKeys`). -/
  errors : Array String
  /-- The binary's diagnostics. -/
  cli : Array Diagnostic
  /-- The Lean front end's diagnostics. -/
  hosted : Array Diagnostic := #[]
  /-- With `obligations`, both front ends' obligations dumps, the `fren`
  command's first (`Fren.Core.dump`). -/
  obligations? : Option (String × String) := none
  /-- Both structural theories dumps, compared independently of diagnostics. -/
  theories? : Option (String × String) := none

/-- Error codes and code-less error headlines, without the trailer that
summarizes the static errors that stopped checking. Internal errors are
kept, including those without a location. -/
def errorKeys (diags : Array Diagnostic) : Array String :=
  diags.filterMap fun d =>
    if d.severity == "error" && !FrenTest.Frontends.isStoppedTrailer d then
      some (d.code?.getD (headOf d)) else none

section
private def stopped : Diagnostic :=
  { line := 0, severity := "error", text := Fren.Core.couldNotHeadline }
private def recursionError : Diagnostic :=
  { line := 4, severity := "error", text := "recursive call does not decrease", code? := some "F0447" }
private def internalError : Diagnostic :=
  { line := 0, severity := "error", text := "internal error: the solver did not decide the realizability check" }

-- A structural-recursion error's stopped trailer is not another error.
#guard errorKeys #[recursionError, stopped] == #["F0447"]
-- Code-less internal errors remain visible, with or without static errors
-- and whether or not they have a location.
#guard errorKeys #[internalError] == #[internalError.text]
#guard errorKeys #[recursionError, internalError, stopped] == #["F0447", internalError.text]
#guard errorKeys #[{ internalError with line := 7 }] == #[internalError.text]
-- Failed comparisons count; warnings do not.
#guard errorKeys #[{ recursionError with code? := some "F0603" },
  { internalError with severity := "warning" }] == #["F0603"]
end

/-- `out` without its obligations dump, and the dump, if it has one
(`Fren.Core.dumpStart`). -/
def splitDump (out : String) (start := Fren.Core.dumpStart) (stop := Fren.Core.dumpEnd) : String × Option String := Id.run do
  let lines := out.splitOn "\n"
  let some i := lines.idxOf? start | return (out, none)
  let some j := (lines.drop i).idxOf? stop | return (out, none)
  let dump := "\n".intercalate ((lines.drop i).take (j + 1))
  return ("\n".intercalate (lines.take i ++ lines.drop (i + j + 1)), some dump)

/-- The `fren` command's diagnostics, summary, exit code and structural
theories; with `obligations`, its obligations dump too. -/
def runCli (path : System.FilePath) (text : String) (obligations := false) :
    IO (Array Diagnostic × Option String × UInt32 × Option String × Option String) := do
  IO.FS.writeFile path text
  let (out, code) ← IO.FS.withIsolatedStreams (FrenCli.check { files := #[path.toString], dumpObligations := obligations, dumpTheories := true })
  let (out, dump?) := splitDump out
  let (out, theories?) := splitDump out Fren.Core.theoriesStart Fren.Core.theoriesEnd
  let (cli, cliSum) := FrenTest.Ui.cliDiagnostics path.toString out (keepUnlocated := true)
  return (cli, cliSum, code, dump?, theories?)

/-- Checks `text` with both front ends, both misreading models if
`misread`, as `--confirm` has them (`Fren.Core.misreadSet`), or if
`FREN_MISREAD_MODELS` is set; with `obligations`, with their obligations
dumps, which, like the structural theories, are not among their diagnostics. -/
def runFrontends (env : Environment) (path : System.FilePath) (text : String) (misread := false) (obligations := false) :
    IO Ran := do
  Fren.Core.misreadSet.set misread
  let misread ← Fren.Core.misreadModels
  let (cli, cliSum, code, cliDump?, cliTheories?) ← runCli path text obligations
  let opts := Fren.fren.dump.set {} (if obligations then "theories,obligations" else "theories")
  let (hosted, hostedSum) ← FrenTest.Ui.hostedDiagnostics env path.toString text opts
  let (dumps, hosted) := hosted.partition (·.text.startsWith Fren.Core.dumpStart)
  let (theories, hosted) := hosted.partition (·.text.startsWith Fren.Core.theoriesStart)
  let theories? := if cliTheories?.isSome || !theories.isEmpty then
      some (cliTheories?.getD "", (theories[0]?.map (·.text)).getD "") else none
  let obligations? := if obligations then some (cliDump?.getD "", (dumps[0]?.map (·.text)).getD "") else none
  let comparison := FrenTest.Frontends.comparison text
    { diags := cli, summary? := cliSum, exit? := some code.toNat } { diags := hosted, summary? := hostedSum } misread
  let render (ds : Array Diagnostic) (s : Option String) :=
    String.join (ds.toList.map fun d => s!"--   {d.line}:{d.col + 1}: {d.severity}{(d.code?.map (s!"[{·}]")).getD ""}: {headOf d}\n")
      ++ s!"--   summary: {s.getD "(none)"}\n"
  return { comparison, reports := s!"-- fren (exit {code}):\n{render cli cliSum}-- Lean:\n{render hosted hostedSum}",
           errors := errorKeys cli,
           cli, hosted, obligations?, theories? }

unsafe def loadFren : IO Environment := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  importModules #[{ module := `Fren }] {} (loadExts := true)

/-- Compares the front ends on the given files, to reproduce or minimize a
difference. -/
unsafe def mainFiles (files : List String) (dir : String) : IO UInt32 := do
  let env ← loadFren
  let mut bad := 0
  for f in files do
    let ran ← runFrontends env (dir / s!"current-files-{← IO.Process.getPID}.fren") (← IO.FS.readFile f)
    let (found, reports) := (ran.comparison.found, ran.reports)
    IO.println s!"{f}: {if found.isEmpty then "the front ends agree" else "the front ends differ"}"
    if let some (a, b) := ran.theories? then
      if a != b then IO.println s!"{f}: structural theories differ (early signal)"
    for x in found do IO.println s!"  {x}"
    unless found.isEmpty do bad := bad + 1; IO.println reports
  return if bad == 0 then 0 else 1

end FrenTest.FuzzFrontends
