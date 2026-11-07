-- keep-sorted start
import FrenTest.FuzzFrontends.Checks
import FrenTest.FuzzFrontends.Obligations
import FrenTest.FuzzFrontends.Results
-- keep-sorted end

open Lean FrenCli FrenCli.Eval
open FrenTest.Ui (Diagnostic)
open FrenTest.Frontends (Report maskBetween headOf)

namespace FrenTest.FuzzFrontends

/-- Checks the specs of seeds `[seed, seed + count)` in this process,
writing each one's outcome to the results file. With `compareDumps`
(`--obligations`), it compares the front ends' obligations dumps too, from
runs with the dump on. Structural theories are always compared as an early
signal; differences are written separately and do not replace diagnostics. -/
unsafe def worker (count seed : Nat) (run : Run) (mode : Mode) (compareDumps : Bool) : IO UInt32 := do
  let env ← loadFren
  let reporter ← IO.asTask (prio := .dedicated) (reportSolverTime run)
  for i in [0:count] do
    let s := seed + i
    -- The spec, and the time in queries that timed out before it.
    let solver0 ← Fren.Core.solverTimeoutMs
    IO.FS.writeFile run.progress s!"{s}\n{solver0}"
    let text : String := mode.spec s
    let t0 ← IO.monoMsNow
    let ran ← runFrontends env run.spec text mode.confirm compareDumps
    let problems := freshProblems mode ran
    let (found, flaky, reports, errs) := (ran.comparison.found ++ problems,
      problems.isEmpty && ran.comparison.flaky, ran.reports, ran.errors)
    -- The obligations dumps, compared without their metadata, and both
    -- written where they differ.
    let obligations := match ran.obligations? with
      | some (a, b) => obligationsDiffer a b
      | none => false
    let obligationsBeyondNames := match ran.obligations? with
      | some (a, b) => obligations && obligationsDifferBeyondNames a b
      | none => false
    if let (true, some (a, b)) := (obligations, ran.obligations?) then
      IO.FS.writeFile (run.dir / s!"obligations-seed{s}.fren")
        (s!"-- fren_fuzz_frontends{flags mode} --obligations --seed {s}\n" ++ text)
      IO.FS.writeFile (run.dir / s!"obligations-seed{s}.cli") a
      IO.FS.writeFile (run.dir / s!"obligations-seed{s}.lean") b
    let theories := ran.theories?.any fun (a, b) => a != b
    if let (true, some (a, b)) := (theories, ran.theories?) then
      IO.FS.writeFile (run.dir / s!"theories-seed{s}.fren") text
      IO.FS.writeFile (run.dir / s!"theories-seed{s}.cli") a
      IO.FS.writeFile (run.dir / s!"theories-seed{s}.lean") b
    let elapsed := (← IO.monoMsNow) - t0
    let timedOut := (← Fren.Core.solverTimeoutMs) - solver0
    if elapsed > slowMs then IO.eprintln s!"seed {s}: slow, {elapsed / 1000}s, {timedOut / 1000}s of it in queries that timed out"
    let issues := found.map fun f => (knownIssue? mode (sharedStaticErrorLines ran.cli ran.hosted) found f).getD 0
    let status := if found.isEmpty then "ok" else if flaky then "inconclusive"
      else if mode.avoidKnown && issues.all (· != 0) then "known" else "differ"
    unless found.isEmpty do
      let pre := if status == "differ" then "" else s!"{status}-"
      let file : System.FilePath := run.dir / s!"{pre}fe-seed{s}.fren"
      let header := String.join (found.toList.map fun f => s!"-- {f.replace "\n" " "}\n")
      IO.FS.writeFile file (s!"-- fren_fuzz_frontends{flags mode} --seed {s}\n" ++ header ++ reports ++ text)
      let why := match status with
        | "inconclusive" => " (only in inconclusive results)"
        | "known" => " (only in known kinds)"
        | _ => ""
      IO.eprintln s!"seed {s}: front ends differ{why}, written to {file}"
      for f in found.extract 0 4 do IO.eprintln s!"  {f}"
    record run { seed := s, status, flags := flags mode, errors := errs.toList.eraseDups.toArray,
                 signatures := found.map signature, issues, ms := elapsed, solverTimeoutMs := timedOut, obligations,
                 obligationsBeyondNames, theories }
    -- Between specs, a crash is no spec's.
    IO.FS.writeFile run.progress ""
  IO.cancel reporter
  let _ ← IO.wait reporter
  return 0

end FrenTest.FuzzFrontends
