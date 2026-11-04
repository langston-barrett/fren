-- keep-sorted start
import FrenCli.Run
-- keep-sorted end

/-! Checks of mutation runs, independent of the command's decision ledger. -/

namespace FrenTest.MutateDecisions

structure Run where
  decisions : Array FrenCli.Decision
  /-- Diagnostics and summary on stderr, apart from stdout's kill rates. -/
  output : String := ""
  code : UInt32 := 0

/-- Capture diagnostics separately from stdout's kill rates: a procedure
name may itself start with `error`. -/
def capture (decisions : IO.Ref (Array FrenCli.Decision)) (command : IO UInt32) : IO Run := do
  let stderr ← IO.mkRef { : IO.FS.Stream.Buffer }
  let (_, code) ← IO.withStderr (IO.FS.Stream.ofBuffer stderr) <|
    IO.FS.withIsolatedStreams command (isolateStderr := false)
  return { decisions := ← decisions.get, output := String.fromUTF8! (← stderr.get).data, code }

/-- Exact identifier multisets, including empty selections. Exit 3 is
expected only when a mutant survives; errors and all other nonzero exits
fail, even if the identifiers and outcomes look right. -/
def problems (selected : Array String) (run : Run) : Array String := Id.run do
  let mut failures := #[]
  let ids := run.decisions.map (·.id)
  if ids.qsort (· < ·) != selected.qsort (· < ·) then
    failures := failures.push s!"decision IDs differ from selected mutants: expected {selected.toList}, got {ids.toList}"
  let expected : UInt32 := if run.decisions.any (·.outcome == .survived) then 3 else 0
  if run.code != expected then
    failures := failures.push s!"`fren mutate` exits with {run.code}, expected {expected}\n{run.output}"
  if (run.output.splitOn "\n").any (·.startsWith "error") then
    failures := failures.push s!"`fren mutate` reports an error:\n{run.output}"
  return failures

private def killed (ids : Array String) : Run :=
  { decisions := ids.map fun id => { id, outcome := .killed, killers := #[("c", "expect:e")] } }

-- Every other assertion (adequacy, outcome and killer agreement) passes
-- for these killed decisions. Dropping/duplicating one must still fail
-- in the full run, the sample, each shard, and the derivative runs.
private def modes : Array (Array String) :=
  let all := (#["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l"]).map fun id =>
    { (default : FrenCli.Mutate.Mutant) with id }
  let select (sample? := none) (shard? := none) :=
    (FrenCli.Mutate.select all none #[] sample? 0 (shard? := shard?)).map (·.id)
  #[select, select (some (all.size / 2))]
    ++ (Array.range 3).map (fun k => select (shard? := some (k, 3)))
    ++ #[(select).map (· ++ "'"), select (some 4)]

#guard modes.all (!·.isEmpty)
#guard modes.all fun selected => (problems selected (killed selected)).isEmpty
#guard modes.all fun selected => selected.all fun id =>
  !(problems selected (killed (selected.filter (· != id)))).isEmpty
#guard modes.all fun selected => selected.all fun id =>
  !(problems selected (killed (selected.push id))).isEmpty
#guard modes.all fun selected => (FrenCli.Mutate.decisionError? selected selected).isNone
#guard modes.all fun selected => (FrenCli.Mutate.decisionError? selected selected.pop).isSome
#guard modes.all fun selected => (FrenCli.Mutate.decisionError? selected (selected.push selected[0]!)).isSome

-- An ID missing from both the baseline and its shard defeats comparison
-- against the baseline alone. Each independent selection detects it.
#guard Id.run do
  let full := modes[0]!
  let id := full[0]!
  let shard := ((modes.extract 2 5).find? (·.contains id)).getD #[]
  return !(problems full (killed (full.filter (· != id)))).isEmpty &&
    !(problems shard (killed (shard.filter (· != id)))).isEmpty
-- A nonempty-selected sample cannot return nothing.
#guard !(problems modes[1]! (killed #[])).isEmpty
#guard (FrenCli.Mutate.decisionError? modes[1]! #[]).isSome
#guard (problems #[] (killed #[])).isEmpty
#guard !(problems #["a"] (killed #["unexpected"])).isEmpty
#guard (FrenCli.Mutate.decisionError? #["a"] #["unexpected"]).isSome
-- Equal totals cannot hide one dropped ID and one duplicated ID.
#guard !(problems #["a", "b"] (killed #["a", "a"])).isEmpty
-- Neither a correct ID multiset nor exit 0 hides an error diagnostic.
#guard !(problems #["a"] { killed #["a"] with output := "error: internal error: probe\n" }).isEmpty
#guard !(problems #["a"] { killed #["a"] with output := "error[F0001]: probe\n" }).isEmpty
#guard (#[1, 2, 3, 4, 255] : Array UInt32).all fun code =>
  !(problems #["a"] { killed #["a"] with code }).isEmpty
#guard (problems #["a"] { decisions := #[{ id := "a", outcome := .survived, killers := #[] }], code := 3 }).isEmpty
#guard !(problems #["a"] { decisions := #[{ id := "a", outcome := .survived, killers := #[] }] }).isEmpty
#guard (FrenCli.Mutate.decisionError? #[] #[]).isNone
#guard (FrenCli.Mutate.decisionError? #[] #["a"]).isSome

#eval show IO Unit from do
  let decisions ← IO.mkRef (killed #["a"]).decisions
  let run ← capture decisions do
    IO.println "error: 1 of 1 mutant killed (100%)"
    pure 0
  unless (problems #["a"] run).isEmpty do
    throw (IO.userError "a kill rate on stdout was mistaken for an error")
  let run ← capture decisions do
    IO.eprintln "error: internal error: probe"
    pure 0
  if (problems #["a"] run).isEmpty then
    throw (IO.userError "an error on stderr was lost")

end FrenTest.MutateDecisions
