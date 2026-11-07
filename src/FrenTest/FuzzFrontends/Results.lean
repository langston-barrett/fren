-- keep-sorted start
import FrenCore.SolverTime
import Lean
-- keep-sorted end

open Lean

namespace FrenTest.FuzzFrontends

/-- How long a spec runs, in milliseconds, before it is reported as slow. -/
def slowMs : Nat := 20000

/-- What a worker found on one spec, one JSON object per line of the run's
results file, so that a worker that crashes loses nothing. -/
structure Outcome where
  seed : Nat
  /-- `ok`, `differ`, `inconclusive` (differ only in undecided checks),
  `known` (with `--avoid-known`, differ only in kinds that
  `knownDifferences` or `knownKinds` lists), `crash` or `timeout`. -/
  status : String
  /-- The mode's flags, as `flags` gives them. -/
  flags : String := ""
  errors : Array String := #[]
  signatures : Array String := #[]
  /-- For each of `signatures`, the issue of its known kind
  (`knownIssue?`), or 0 if it is of none. -/
  issues : Array Nat := #[]
  /-- How long the spec took, in milliseconds, and how much of that was in
  solver queries that ended at their time limit (`Fren.Core.solverTimeoutMs`). -/
  ms : Nat := 0
  solverTimeoutMs : Nat := 0
  /-- Whether the front ends' obligations dumps differ, without their
  metadata (`Fren.Core.withoutMetadata`): reported, but not a failure
  (`obligationsDiffer`). -/
  obligations : Bool := false
  /-- Structural differences are an early signal, independently of diagnostics. -/
  theories : Bool := false
  /-- And whether they differ other than in the names of their constants
  (`obligationsDifferBeyondNames`). -/
  obligationsBeyondNames : Bool := false
  deriving ToJson, FromJson

/-- A run's work files, named after the driver's process, so that runs
sharing `--out` do not mix them. -/
structure Run where
  dir : String
  id : String

def Run.results (r : Run) : System.FilePath := r.dir / s!"results-{r.id}.jsonl"
def Run.progress (r : Run) : System.FilePath := r.dir / s!"current-{r.id}.seed"
def Run.spec (r : Run) : System.FilePath := r.dir / s!"current-{r.id}.fren"
/-- The worker's `Fren.Core.solverTimeoutMs`, which it writes as it grows. -/
def Run.solver (r : Run) : System.FilePath := r.dir / s!"current-{r.id}.solver"

/-- Writes the worker's `Fren.Core.solverTimeoutMs` to `Run.solver` whenever
it grows, until cancelled, on a thread of its own, so that it is written
while a spec's check runs, or hangs. The file is replaced whole, so that
the driver never reads half of it. -/
def reportSolverTime (r : Run) : IO Unit := do
  let mut last := 0
  let tmp := r.solver.addExtension "tmp"
  while !(← IO.checkCanceled) do
    let ms ← Fren.Core.solverTimeoutMs
    if ms != last then
      IO.FS.writeFile tmp (toString ms)
      IO.FS.rename tmp r.solver
      last := ms
    IO.sleep 100

def record (r : Run) (o : Outcome) : IO Unit := do
  let h ← IO.FS.Handle.mk r.results .append
  h.putStrLn (toJson o).compress
  h.flush

/-- Counts `x` in a tally. -/
def tally (xs : Array (String × Nat × Nat)) (x : String) (seed : Nat) : Array (String × Nat × Nat) :=
  match xs.findIdx? (·.1 == x) with
  | some k => xs.modify k fun (x, n, first) => (x, n + 1, first)
  | none => xs.push (x, 1, seed)

/-- The outcomes of a results file's text, one to a line. -/
def parseOutcomes (text : String) : Array Outcome :=
  (text.splitOn "\n").toArray.filterMap fun l => (Json.parse l >>= fromJson? : Except String Outcome).toOption

/-- The outcomes recorded so far in a run. -/
def outcomesOf (run : Run) : IO (Array Outcome) := do
  return parseOutcomes (← IO.FS.readFile run.results)

end FrenTest.FuzzFrontends
