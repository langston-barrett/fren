-- keep-sorted start
import FrenTest.FuzzFrontends.Results
-- keep-sorted end

open Lean

namespace FrenTest.FuzzFrontends

/-! ### The report of a run -/

/-- The file where a run writes the spec of an outcome, if it writes one. -/
def Outcome.file? (o : Outcome) : Option String :=
  match o.status with
  | "differ" => some s!"fe-seed{o.seed}.fren"
  | "known" | "inconclusive" => some s!"{o.status}-fe-seed{o.seed}.fren"
  | "crash" | "timeout" => some s!"{o.status}-seed{o.seed}.fren"
  | _ => none

/-- Whether an outcome fails the run: a difference of a kind that is not
known, a crash or a timeout. -/
def Outcome.fails (o : Outcome) : Bool := o.status ∈ ["differ", "crash", "timeout"]

/-- `s` in a cell of a Markdown table. -/
def mdCell (s : String) : String := (s.replace "\n" " ").replace "|" "\\|" |>.replace "<" "&lt;"

/-- The kinds of an outcome's differences, each with its issue, or as new
if it is of no known kind. -/
def Outcome.kinds (o : Outcome) : String :=
  "<br>".intercalate (o.signatures.toList.zipIdx.map fun (g, i) =>
    let issue := o.issues[i]?.getD 0
    (if issue == 0 then "**new**: " else s!"#{issue}: ") ++ mdCell g)

/-- A Markdown report of a run's outcomes, for the job's summary: how many
specs of each outcome; each one that fails it, with its kinds; each
known kind, with its issue, how many specs had it, and their seeds; and
each slow spec (`slowMs`), with how long it took in queries that timed
out. The specs are named as the run writes them. -/
def report (outcomes : Array Outcome) : String := Id.run do
  let n (st : String) := (outcomes.filter (·.status == st)).size
  let mut out := s!"{outcomes.size} specs: {n "differ"} differ in a kind that is not known, {n "crash"} crashed and \
    {n "timeout"} took too long, which fail the job; {n "known"} differ only in known kinds, and \
    {n "inconclusive"} only in inconclusive results.\n"
  let theories := outcomes.filter (·.theories)
  unless theories.isEmpty do
    out := out ++ s!"\n{theories.size} specs' structural theories differ (early signal; `theories-seed*`).\n"
  let dumps := outcomes.filter (·.obligations)
  unless dumps.isEmpty do
    out := out ++ s!"\n{dumps.size} specs' obligations dumps differ, {(dumps.filter (·.status == "ok")).size} of them \
      where the messages agree, and {(dumps.filter (·.obligationsBeyondNames)).size} other than in the names of their \
      constants, which fails nothing (`obligations-seed*`).\n"
  let failed := outcomes.filter (·.fails) |>.qsort (·.seed < ·.seed)
  unless failed.isEmpty do
    out := out ++ "\n#### Failures\n\n| Seed | Flags | Outcome | Spec | Kinds |\n|---|---|---|---|---|\n"
    for o in failed do
      let fl := o.flags.trimAscii.toString
      let fl := if fl.isEmpty then "" else s!"`{fl}`"
      out := out ++ s!"| {o.seed} | {fl} | {o.status} | `{(o.file?).getD ""}` | {o.kinds} |\n"
  -- Each known kind, with its issue, and the seeds of the specs that have it.
  let mut kinds : Array (String × Nat × Array Nat) := #[]
  for o in outcomes.qsort (·.seed < ·.seed) do
    for (g, i) in o.signatures.toList.zipIdx do
      let issue := o.issues[i]?.getD 0
      if issue == 0 then continue
      kinds := match kinds.findIdx? fun (g', j, _) => g' == g && j == issue with
        | some k => kinds.modify k fun (g, j, seeds) =>
          (g, j, if seeds.contains o.seed then seeds else seeds.push o.seed)
        | none => kinds.push (g, issue, #[o.seed])
  unless kinds.isEmpty do
    out := out ++ "\n#### Known kinds\n\n| Kind | Issue | Specs | Seeds |\n|---|---|---|---|\n"
    for (g, issue, seeds) in kinds.qsort (·.2.2.size > ·.2.2.size) do
      let shown := ", ".intercalate ((seeds.extract 0 5).toList.map toString) ++ if seeds.size > 5 then ", …" else ""
      out := out ++ s!"| {mdCell g} | #{issue} | {seeds.size} | {shown} |\n"
  let inconclusive := outcomes.filter (·.status == "inconclusive")
  unless inconclusive.isEmpty do
    let seeds := ", ".intercalate (inconclusive.toList.map (toString ·.seed))
    out := out ++ s!"\nOnly in inconclusive results: seeds {seeds}.\n"
  -- The slow specs, slowest first, with the time in queries that timed out,
  -- which the time limit leaves out (`SpecTimeout.overdue`).
  let slow := outcomes.filter (·.ms > slowMs) |>.qsort (·.ms > ·.ms)
  unless slow.isEmpty do
    out := out ++ "\n#### Slow specs\n\n| Seed | Flags | Outcome | Time | In queries that timed out |\n|---|---|---|---|---|\n"
    for o in slow do
      let fl := o.flags.trimAscii.toString
      let fl := if fl.isEmpty then "" else s!"`{fl}`"
      out := out ++ s!"| {o.seed} | {fl} | {o.status} | {o.ms / 1000} s | {o.solverTimeoutMs / 1000} s |\n"
  return out

section
private def kn : Outcome :=
  { seed := 7, status := "known", flags := " --avoid-known", signatures := #["k"], issues := #[493] }
private def df : Outcome :=
  { seed := 5, status := "differ", flags := " --avoid-known", signatures := #["a|b", "k"], issues := #[0, 493] }
-- A clean run reports only its counts.
#guard (report #[{ seed := 1, status := "ok", theories := true }]).contains
  "1 specs' structural theories differ (early signal; `theories-seed*`).".toSlice
#guard report #[{ seed := 1, status := "ok" }] == "1 specs: 0 differ in a kind that is not known, 0 crashed and \
  0 took too long, which fail the job; 0 differ only in known kinds, and 0 only in inconclusive results.\n"
-- Specs whose obligations dumps differ are counted, but fail nothing.
#guard report #[{ seed := 1, status := "ok", obligations := true }, { seed := 2, status := "known", obligations := true }] ==
  "2 specs: 0 differ in a kind that is not known, 0 crashed and 0 took too long, which fail the job; 1 differ only in \
  known kinds, and 0 only in inconclusive results.\n\n2 specs' obligations dumps differ, 1 of them where the messages \
  agree, and 0 other than in the names of their constants, which fails nothing (`obligations-seed*`).\n"
-- A failing spec is listed with its kinds, new or known, and every known
-- kind with its issue and seeds, of the failing specs too.
#guard ((report #[kn, df, { seed := 9, status := "crash" }]).splitOn "\n").drop 6 == [
  "| 5 | `--avoid-known` | differ | `fe-seed5.fren` | **new**: a\\|b<br>#493: k |",
  "| 9 |  | crash | `crash-seed9.fren` |  |",
  "", "#### Known kinds", "", "| Kind | Issue | Specs | Seeds |", "|---|---|---|---|",
  "| k | #493 | 2 | 5, 7 |", ""]
#guard !kn.fails && df.fails
-- A slow spec is listed, with the time in queries that timed out.
#guard ((report #[{ seed := 3, status := "ok", ms := 41000, solverTimeoutMs := 40000 },
  { seed := 4, status := "ok", ms := 19000 }]).splitOn "\n").drop 2 == [
  "#### Slow specs", "", "| Seed | Flags | Outcome | Time | In queries that timed out |", "|---|---|---|---|---|",
  "| 3 |  | ok | 41 s | 40 s |", ""]
end

/-- The outcomes of every run whose results are in `dir`. -/
def outcomesIn (dir : System.FilePath) : IO (Array Outcome) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if e.fileName.startsWith "results-" && e.fileName.endsWith ".jsonl" then
      out := out ++ parseOutcomes (← IO.FS.readFile e.path)
  return out

end FrenTest.FuzzFrontends
