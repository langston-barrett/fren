-- keep-sorted start
import FrenTest.FuzzFrontends.Report
import FrenTest.FuzzFrontends.Worker
import FrenTest.SpecTimeout
-- keep-sorted end

open Lean

namespace FrenTest.FuzzFrontends

/-- The most specs that one worker checks, a workaround for #650: a
worker slows down as it checks more, since the hosted front end's memory
grows by some 90 MB a spec (on macOS; the binary's stays level), so that
four workers of 100 specs would need more than a CI runner's 16 GB. On
CI, a worker's 97th and 98th specs, which take under a second on their
own, took 22 s and more than 30 s (seeds 1202247 and 1202248). A fresh
worker, which takes a few seconds to start, takes over after these. Once
#650 is fixed, this is to be raised, or the replacement dropped. -/
def workerSpecs : Nat := 25

/-- Runs workers until every seed is checked. The solver can abort the
process (a failed assertion in cvc5), so specs run in a worker, and a
crash is recorded as the outcome of the spec it was checking. A spec that
takes longer than `limit` seconds is stopped and recorded as a timeout.
Crashes and timeouts are findings: the run then exits nonzero. A worker
that dies while checking no spec, before its first or between two, is
blamed on none: the run resumes after the last spec recorded, or stops if
the worker recorded none. With `compareDumps`, the workers compare the
obligations dumps too (`worker`). -/
unsafe def mainFrontends (count seed : Nat) (dir : String) (mode : Mode) (limit : Nat) (compareDumps : Bool) :
    IO UInt32 := do
  let start ← IO.monoMsNow
  let run : Run := { dir, id := toString (← IO.Process.getPID) }
  IO.FS.writeFile run.results ""
  let mut next := seed
  -- The appended enumeration groups put more declarations in each spec;
  -- restart their workers sooner to keep the retained environments small.
  let perWorker := if mode.enumerationObligations || mode.enumerationRelations then workerSpecs / 2 else workerSpecs
  while next < seed + count do
    IO.FS.writeFile run.progress ""
    let batch := min (seed + count - next) perWorker
    let args := #["--worker", run.id, "--count", toString batch, "--seed", toString next, "--out", dir]
      ++ mode.args ++ (if compareDumps then #["--obligations"] else #[])
    for f in [run.solver, run.solver.addExtension "tmp"] do
      try IO.FS.removeFile f catch _ => pure ()
    let child ← IO.Process.spawn { cmd := (← IO.appPath).toString, args, stdin := .null, stdout := .inherit, stderr := .inherit }
    -- Wait, and stop the worker if one spec takes too long, leaving out its
    -- queries that timed out (`SpecTimeout.overdue`).
    let mut current := ""
    let mut since ← IO.monoMsNow
    let mut solver := 0
    let mut code? : Option UInt32 := none
    let mut timedOut := false
    let mut spent := (0, 0)
    repeat
      if let some c ← child.tryWait then code? := some c; break
      let now ← IO.monoMsNow
      let cur := (← (IO.FS.readFile run.progress).toBaseIO).toOption.getD current
      solver := (← (IO.FS.readFile run.solver).toBaseIO).toOption.bind (·.trimAscii.toString.toNat?) |>.getD solver
      let atStart := (((current.splitOn "\n")[1]?).bind (·.toNat?)).getD 0
      if cur != current then current := cur; since := now
      else if FrenTest.SpecTimeout.overdue limit (now - since) (solver - atStart) && !current.isEmpty then
        child.kill
        let _ ← child.wait
        timedOut := true
        spent := (now - since, solver - atStart)
        break
      IO.sleep 200
    if code? == some 0 then next := next + batch; continue
    let some failed := ((← IO.FS.readFile run.progress).splitOn "\n").head!.trimAscii.toString.toNat?
      | let done := (← outcomesOf run).filter (fun o => next ≤ o.seed && o.seed < seed + count)
        let last? := done.foldl (fun m o => some (max (m.getD o.seed) o.seed)) none
        let some last := last?
          | IO.eprintln s!"fren_fuzz_frontends: the worker for seed {next} exited ({code?.getD 0}) before checking any spec"
            return 2
        IO.eprintln s!"seed {last + 1}: the worker exited ({code?.getD 0}) between specs; resuming"
        next := last + 1
        continue
    let what := if timedOut then s!"took more than {limit}s, leaving out {spent.2 / 1000}s in queries that timed out"
      else s!"crashed (exit {code?.getD 0})"
    IO.eprintln s!"seed {failed}: the worker {what}"
    let text : String := mode.spec failed
    let kind := if timedOut then "timeout" else "crash"
    IO.FS.writeFile (dir / s!"{kind}-seed{failed}.fren") (s!"-- fren_fuzz_frontends{flags mode} --seed {failed}: {what}\n" ++ text)
    record run { seed := failed, status := kind, flags := flags mode, ms := spent.1, solverTimeoutMs := spent.2 }
    next := failed + 1
  let outcomes ← outcomesOf run
  for f in [run.progress, run.spec, run.solver, run.solver.addExtension "tmp"] do
    try IO.FS.removeFile f catch _ => pure ()
  let mut sigs := #[]
  let mut codes := #[]
  for o in outcomes do
    for g in o.signatures do sigs := tally sigs g o.seed
    for e in o.errors do codes := tally codes e o.seed
  unless sigs.isEmpty do
    IO.eprintln "differences, by kind (how many, and the first seed):"
    for (g, n, first) in sigs.qsort (·.2.1 > ·.2.1) do IO.eprintln s!"  {n} × seed {first}: {g}"
  let n (st : String) := (outcomes.filter (·.status == st)).size
  let codeList := ", ".intercalate ((codes.qsort (·.2.1 > ·.2.1)).toList.map fun (e, k, _) => s!"{e} ×{k}")
  IO.eprintln s!"specs with errors from `fren check`: {(outcomes.filter (!·.errors.isEmpty)).size} ({codeList})"
  IO.eprintln s!"specs whose structural theories differ (early signal): {(outcomes.filter (·.theories)).size} (`theories-seed*` in {dir})"
  let dumps := outcomes.filter (·.obligations)
  if compareDumps then
    IO.eprintln s!"specs whose obligations dumps differ, which fails nothing: {dumps.size}, \
      {(dumps.filter (·.status == "ok")).size} of them where the messages agree, \
      {(dumps.filter (·.obligationsBeyondNames)).size} other than in the names of their constants \
      (`obligations-seed*` in {dir})"
  IO.eprintln s!"fren_fuzz_frontends: {outcomes.size} specs in {((← IO.monoMsNow) - start) / 1000}s, {n "differ"} where \
    the front ends differ, {n "inconclusive"} more only in inconclusive results, \
    {n "known"} more only in known kinds, {n "crash"} crashed, \
    {n "timeout"} took more than {limit}s outside queries that timed out (results in {run.results})"
  return if n "differ" + n "crash" + n "timeout" == 0 then 0 else 1

def usage : String :=
  "usage: fren_fuzz_frontends [--count N] [--seed N] [--out DIR] [--avoid-known] [--guards] [--sites] [--confirm] [--obligations] [--scrutinees] [--inductions] [--induction-forms] [--keywords] [--fact-scopes] [--induction-candidates] [--decidable] [--enumeration-obligations] [--enumeration-relations] [--unfoldings] [--datatype-elements] [--generic-functions] [--set-card] [--set-card-fallback] [--recursion-positions] [--mutual-groups] [--spec-timeout SECONDS]\n" ++
  "       fren_fuzz_frontends --files FILE...\n" ++
  "       fren_fuzz_frontends --report DIR\n" ++
  "       fren_fuzz_frontends [--avoid-known] [--guards] [--sites] [--confirm] [--scrutinees] [--inductions] [--induction-forms] [--keywords] [--fact-scopes] [--induction-candidates] [--decidable] [--enumeration-obligations] [--enumeration-relations] [--unfoldings] [--datatype-elements] [--generic-functions] [--set-card] [--set-card-fallback] [--recursion-positions] [--mutual-groups] --print SEED"

structure Opts where
  count : Nat := 100
  seed : Nat := 0
  dir : String := ".lake/fuzz"
  limit : Nat := 30
  worker? : Option String := none
  /-- Compare the obligations dumps too (`--obligations`, `worker`). -/
  compareDumps : Bool := false

unsafe def main (args : List String) : IO UInt32 := do
  if let "--files" :: files := args then
    IO.FS.createDirAll ".lake/fuzz"
    return ← mainFiles files ".lake/fuzz"
  let mode : Mode := { avoidKnown := args.contains "--avoid-known", guards := args.contains "--guards"
                       sites := args.contains "--sites", confirm := args.contains "--confirm", scrutinees := args.contains "--scrutinees"
                       inductions := args.contains "--inductions", inductionForms := args.contains "--induction-forms"
                       keywords := args.contains "--keywords", factScopes := args.contains "--fact-scopes"
                       inductionCandidates := args.contains "--induction-candidates"
                       decidable := args.contains "--decidable"
                       enumerationObligations := args.contains "--enumeration-obligations"
                       enumerationRelations := args.contains "--enumeration-relations"
                       unfoldings := args.contains "--unfoldings", datatypeElements := args.contains "--datatype-elements"
                       genericFunctions := args.contains "--generic-functions"
                       setCard := args.contains "--set-card", setCardFallback := args.contains "--set-card-fallback", recursionPositions := args.contains "--recursion-positions", mutualGroups := args.contains "--mutual-groups" }
  let args := args.filter (fun a => a != "--avoid-known" && a != "--guards" && a != "--sites" && a != "--confirm" && a != "--scrutinees"
    && a != "--inductions" && a != "--induction-forms" && a != "--keywords" && a != "--fact-scopes" && a != "--induction-candidates"
    && a != "--decidable" && a != "--enumeration-obligations" && a != "--enumeration-relations" && a != "--unfoldings" && a != "--datatype-elements" && a != "--generic-functions" && a != "--set-card" && a != "--set-card-fallback" && a != "--recursion-positions" && a != "--mutual-groups")
  if let ["--report", dir] := args then
    IO.print (report (← outcomesIn dir))
    return 0
  if let ["--print", n] := args then
    let some s := n.toNat? | IO.eprintln usage; return 2
    IO.print (mode.spec s)
    return 0
  let rec parse : List String → Opts → Option Opts
    | [], o => some o
    | "--count" :: n :: rest, o => n.toNat?.bind fun n => parse rest { o with count := n }
    | "--seed" :: n :: rest, o => n.toNat?.bind fun n => parse rest { o with seed := n }
    | "--out" :: d :: rest, o => parse rest { o with dir := d }
    | "--spec-timeout" :: n :: rest, o => n.toNat?.bind fun n => parse rest { o with limit := n }
    | "--worker" :: id :: rest, o => parse rest { o with worker? := some id }
    | "--obligations" :: rest, o => parse rest { o with compareDumps := true }
    | _, _ => none
  let some o := parse args {} | IO.eprintln usage; return 2
  IO.FS.createDirAll o.dir
  match o.worker? with
  | some id => worker o.count o.seed { dir := o.dir, id } mode o.compareDumps
  | none => mainFrontends o.count o.seed o.dir mode o.limit o.compareDumps

end FrenTest.FuzzFrontends
