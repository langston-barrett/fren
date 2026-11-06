-- keep-sorted start
import FrenCore.Obligations
-- keep-sorted end

open Lean

namespace FrenTest.FuzzFrontends

/-- Whether two front ends' obligations dumps of a spec differ, but for
their metadata (`Fren.Core.withoutMetadata`): an early signal of a
difference between their queries (`Reqs/Cli#obligations`), which a run
reports, but which fails nothing yet, since many dumps differ in what
predates the dump, such as the names that lean-smt's embeddings give
`Nat` and `Bool` variables (#493). -/
def obligationsDiffer (cli hosted : String) : Bool :=
  Fren.Core.withoutMetadata cli != Fren.Core.withoutMetadata hosted

/-- `line` with each of its symbols that `names` has written `_`. -/
def collapseNames (names : Array String) (line : String) : String := Id.run do
  let mut out := ""
  let mut tok := ""
  for c in line.toList do
    if c == ' ' || c == '(' || c == ')' then
      out := out ++ (if names.contains tok then "_" else tok) |>.push c
      tok := ""
    else tok := tok.push c
  return out ++ (if names.contains tok then "_" else tok)

/-- A dump's obligations, each as its lines, sorted, with the names of the
constants and functions that it declares written `_` (`collapseNames`): two dumps whose
obligations are the same so differ only in the names of their constants,
as where lean-smt's embeddings rename a `Nat` or `Bool` variable. -/
def namelessObligations (dump : String) : Array (Array String) := Id.run do
  let mut blocks : Array (Array String) := #[]
  for l in (Fren.Core.withoutMetadata dump).splitOn "\n" do
    if l == "(obligation" then blocks := blocks.push #[]
    else if let some b := blocks.back? then blocks := blocks.pop.push (b.push l)
  return blocks.map fun b =>
    let names := b.filterMap fun l =>
      let l := l.trimAscii.toString
      ((l.dropPrefix? "(declare-const ").orElse fun _ => l.dropPrefix? "(declare-fun ").map
        fun r => ((r.toString.splitOn " ")[0]?).getD ""
    (b.map (collapseNames names)).qsort (· < ·)

/-- Whether two front ends' obligations dumps differ other than in the
names of their constants (`namelessObligations`). -/
def obligationsDifferBeyondNames (cli hosted : String) : Bool :=
  namelessObligations cli != namelessObligations hosted

#guard !obligationsDifferBeyondNames
  "(obligation\n  (signature\n    (declare-const n Int)\n  )\n  (context\n    (>= n 0)\n  )\n  (goal (> n 1))\n)"
  "(obligation\n  (signature\n    (declare-const f Int)\n  )\n  (context\n    (>= f 0)\n  )\n  (goal (> f 1))\n)"
#guard obligationsDifferBeyondNames
  "(obligation\n  (signature\n    (declare-const n Int)\n  )\n  (goal (> n 1))\n)"
  "(obligation\n  (signature\n    (declare-const f Int)\n  )\n  (goal (> f 2))\n)"

end FrenTest.FuzzFrontends
