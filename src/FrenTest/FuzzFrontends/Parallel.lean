import FrenTest.FuzzFrontends.Main

/-!
# Bounded parallel front-end fuzzing

Only the executable uses this schedule. The fixed corpus calls the same
front-end checks directly. Each lane keeps the ordinary supervisor's
crash recovery, progress files and solver timeout accounting.
-/

namespace FrenTest.FuzzFrontends.Parallel

open FrenTest.FuzzFrontends

/-- Run two disjoint, contiguous seed ranges in isolated workers. Restart
more often than in a serial run: two imported environments must fit beside
the retained per-spec environments (see `workerSpecs`). `--jobs 1` retains
the serial schedule for small machines and throughput comparisons. -/
unsafe def run (o : Opts) (mode : Mode) : IO UInt32 := do
  if o.jobs == 1 || o.count < 2 then
    return ← mainFrontends o.count o.seed o.dir mode o.limit o.compareDumps
  let start ← IO.monoMsNow
  let pid ← IO.Process.getPID
  let first := o.count / 2
  let ranges := #[(o.seed, first), (o.seed + first, o.count - first)]
  let cap := if mode.enumerationObligations || mode.enumerationRelations then workerSpecs / 2 else workerSpecs
  let cap := max 1 (cap / 3)
  let mut tasks := #[]
  let mut runs : Array Run := #[]
  for ((seed, count), lane) in ranges.zipIdx do
    let id := s!"{pid}-p{lane}"
    runs := runs.push { dir := o.dir, id }
    tasks := tasks.push (← IO.asTask (prio := .dedicated)
      (mainFrontends count seed o.dir mode o.limit o.compareDumps (some id) (some cap)))
  -- Reap both lanes even if one fails. Each keeps its own append-only
  -- results file, so a stopped run can still be inspected with --report.
  let mut code : UInt32 := 0
  for task in tasks do
    match ← IO.wait task with
    | .ok c => code := max code c
    | .error e => IO.eprintln s!"fren_fuzz_frontends: {e}"; code := 2
  let mut outcomes := #[]
  for run in runs do
    try outcomes := outcomes ++ (← outcomesOf run)
    catch e => IO.eprintln s!"fren_fuzz_frontends: {e}"; code := 2
  let seeds := (outcomes.map (·.seed)).qsort (· < ·)
  unless seeds == (Array.range o.count).map (o.seed + ·) do
    IO.eprintln "fren_fuzz_frontends: incomplete or duplicate parallel results"
    code := 2
  IO.eprintln s!"fren_fuzz_frontends: {outcomes.size} specs in {((← IO.monoMsNow) - start) / 1000}s with 2 jobs (results in {o.dir})"
  return code

end FrenTest.FuzzFrontends.Parallel
