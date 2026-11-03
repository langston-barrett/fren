-- keep-sorted start
import FrenCore.Check
import FrenCore.Evidence
import FrenCore.Names
-- keep-sorted end

/-!
# cvc5's statistics of each query

`fren check --solver-stats` reports, for the queries asked of the
solver, where their time went (`Reqs/dev/Testing#solver-statistics`):
Fren's own measure of each phase of a query, from making its term manager
to freeing it, and cvc5's statistics of its solver, which cvc5 keeps
whether or not anyone reads them (#742). Without the flag, none of this
runs: `FrenCli.solveOn` reads no clock of its own, only the one that
`Fren.Core.timeQuery` reads for every query, and asks cvc5 for nothing
more.

cvc5 reports its statistics as `(get-info :all-statistics)` writes them:
a list of `("name" value)`, where a value is a number, a time such as
`12ms`, or a histogram such as `{ RewriteStep: 108, CnfStep: 11 }`. `parse`
keeps only what the report shows, so that a run's thousands of queries do
not each keep their statistics' whole text.
-/

namespace FrenCli.SolverStats

/-- When a query reached each of its phases, in nanoseconds of the
monotonic clock (`IO.monoNanosNow`), and cvc5's statistics of its solver,
as `solveScript` records them. When a command answers with an error,
`solveOn` sets every mark not yet reached to the time of the failure, so
that its time up to there is in the phases it reached and none is in the
later ones. When something throws instead, as a parse error or a failure
to read the model does, the later marks stay 0, and `Probe.phases` counts
the time since the last mark as `free`; and the statistics are then not
read, so the query's counts are all 0. Fren writes every script, so
neither is expected. A mark left at 0 counts as the one before it
(`Probe.phases`). -/
structure Probe where
  /-- Before the term manager is made. -/
  start : Nat := 0
  /-- Before the first command that initializes the solver's theories
  (`FrenCli.Cvc5.initializes`), or before `checkSat` if none did. -/
  initStart : Nat := 0
  /-- After that command. -/
  initEnd : Nat := 0
  /-- Before and after `checkSat`. -/
  checkStart : Nat := 0
  checkEnd : Nat := 0
  /-- After the model's values are read, if it was wanted. -/
  modelEnd : Nat := 0
  /-- After cvc5's statistics are read. -/
  statsEnd : Nat := 0
  /-- After the solver and its term manager are freed. -/
  stop : Nat := 0
  /-- cvc5's `(get-info :all-statistics)`, or empty if it was not read. -/
  stats : String := ""
  /-- Whether the query ended in an error of the solver's, a command that
  answered with one or a throw, rather than an answer. -/
  failed : Bool := false
  deriving Inhabited

/-- How long each phase of a query took, in nanoseconds. -/
structure Phases where
  /-- The term manager, the solver, its options, the parser, the logic
  and the declarations, up to the first command that initializes the
  solver's theories. -/
  setup : Nat := 0
  /-- That command, in which cvc5 initializes its theories
  (`SolverEngine::finishInit`), the cost that the logic decides. -/
  init : Nat := 0
  /-- The other commands: the assertions and definitions. -/
  assert : Nat := 0
  check : Nat := 0
  /-- Reading the model's values, if it was wanted. -/
  model : Nat := 0
  /-- Freeing the solver and its term manager. -/
  free : Nat := 0
  deriving Inhabited, Repr, BEq

def Phases.total (p : Phases) : Nat := p.setup + p.init + p.assert + p.check + p.model + p.free

def Phases.add (p q : Phases) : Phases :=
  { setup := p.setup + q.setup, init := p.init + q.init, assert := p.assert + q.assert, check := p.check + q.check,
    model := p.model + q.model, free := p.free + q.free }

/-- The phases of a probe, each the time between the marks around it:
the time of reading cvc5's statistics counts for none of them. A mark
left at 0, of a phase never reached, counts as the mark before it. -/
def Probe.phases (p : Probe) : Phases :=
  let initStart := max p.start p.initStart
  let initEnd := max initStart p.initEnd
  let checkStart := max initEnd p.checkStart
  let checkEnd := max checkStart p.checkEnd
  let modelEnd := max checkEnd p.modelEnd
  let statsEnd := max modelEnd p.statsEnd
  let stop := max statsEnd p.stop
  { setup := initStart - p.start, init := initEnd - initStart, assert := checkStart - initEnd,
    check := checkEnd - checkStart, model := modelEnd - checkEnd, free := stop - statsEnd }

-- The 18 ns of reading the statistics count for no phase.
#guard (Probe.mk 10 15 25 30 70 72 90 95 "" false).phases.total == 67
-- A query that threw in its first command that initializes, which began
-- at 15: the time since that mark is in `free`.
#guard (Probe.mk 10 15 0 0 0 0 0 20 "" true).phases == { setup := 5, free := 5 }
-- A query whose assertion failed, at 40, after the first command
-- initialized at 15–25: its assertions are in `assert`, not `free`.
#guard (Probe.mk 10 15 25 40 40 40 40 50 "" true).phases == { setup := 5, init := 10, assert := 15, free := 10 }

/-- What the report shows of cvc5's statistics of one query. Times are
cvc5's, in whole milliseconds. -/
structure Cvc5Stats where
  /-- The SAT solver's (`sat::…`). -/
  decisions : Nat := 0
  conflicts : Nat := 0
  propagations : Nat := 0
  /-- The theories' checks and the rewrites, as the resource manager counts
  them (`resource::steps::resource`'s `TheoryCheckStep` and `RewriteStep`). -/
  theoryChecks : Nat := 0
  rewrites : Nat := 0
  /-- Every theory's lemmas (`theory::T::lemmas`). -/
  lemmas : Nat := 0
  /-- `Instantiate::Instantiations_Total`. -/
  instantiations : Nat := 0
  /-- `resource::resourceUnitsUsed`, as `--resource-limit` counts. -/
  resourceUnits : Nat := 0
  /-- `smt::SolverEngine::processAssertionsTime`: preprocessing, which
  cvc5 does in `checkSat`. -/
  preprocessMs : Nat := 0
  /-- `prop::CnfStream::cnfConversionTime`: the clausal form, within
  `checkSat`. -/
  cnfMs : Nat := 0
  /-- `TheoryEngine::combineTheoriesTime`: theory combination, within
  `checkSat`. -/
  combineMs : Nat := 0
  /-- Each theory's `theory::T::checkTime` that is not 0, as `(T, ms)`. -/
  theoryMs : Array (String × Nat) := #[]
  /-- Each inference that the theories made, by cvc5's name for it, and
  how many times (`resource::steps::inference-id`), that is not 0. -/
  inferences : Array (String × Nat) := #[]
  deriving Inhabited, Repr, BEq

/-- `v` without a trailing `ms`, as a whole number, if it is one. -/
def number? (v : String) : Option Nat :=
  ((v.trimAscii.toString.dropSuffix? "ms").map (·.toString) |>.getD v.trimAscii.toString).toNat?

/-- The entries of a histogram's body, `A: 1, B: 2`, that are whole numbers. -/
def histogram (body : String) : Array (String × Nat) :=
  (body.splitOn ",").toArray.filterMap fun e =>
    match e.splitOn ":" with
    | [k, v] => (number? v).map ((k.trimAscii.toString), ·)
    | _ => none

/-- What the report shows of `text`, cvc5's `(get-info :all-statistics)`. -/
def parse (text : String) : Cvc5Stats := Id.run do
  let mut s : Cvc5Stats := {}
  for piece in (text.splitOn "(\"").drop 1 do
    let name := (piece.takeWhile (· != '"')).toString
    let rest := ((piece.drop (name.length + 1)).trimAsciiStart).toString
    if rest.startsWith "{" then
      let body := ((rest.drop 1).takeWhile (· != '}')).toString
      if name == "resource::steps::inference-id" then
        s := { s with inferences := (histogram body).filter (·.2 != 0) }
      else if name == "resource::steps::resource" then
        for (k, n) in histogram body do
          if k == "TheoryCheckStep" then s := { s with theoryChecks := n }
          if k == "RewriteStep" then s := { s with rewrites := n }
      continue
    let some n := number? (rest.takeWhile (· != ')')).toString | continue
    match name with
    | "sat::decisions" => s := { s with decisions := n }
    | "sat::conflicts" => s := { s with conflicts := n }
    | "sat::propagations" => s := { s with propagations := n }
    | "Instantiate::Instantiations_Total" => s := { s with instantiations := n }
    | "resource::resourceUnitsUsed" => s := { s with resourceUnits := n }
    | "smt::SolverEngine::processAssertionsTime" => s := { s with preprocessMs := n }
    | "prop::CnfStream::cnfConversionTime" => s := { s with cnfMs := n }
    | "TheoryEngine::combineTheoriesTime" => s := { s with combineMs := n }
    | _ =>
      -- `theory::T::lemmas` and `theory::T::checkTime`, and the arrays'
      -- `theory::arrays::theory::arrays::checkTime`.
      match name.splitOn "::" with
      | ["theory", _, "lemmas"] => s := { s with lemmas := s.lemmas + n }
      -- Only these, so that a timer nested within a theory's check, such
      -- as a sub-solver's `theory::T::sub::checkTime`, is not counted twice.
      | ["theory", t, "checkTime"] | ["theory", t, "theory", _, "checkTime"] =>
        if n != 0 then s := { s with theoryMs := s.theoryMs.push (t, n) }
      | _ => pure ()
  return s

#guard parse "(:all-statistics ((\"sat::decisions\" 7) (\"driver::filename\" a b) (\"theory::arith::lemmas\" 1) \
    (\"theory::strings::lemmas\" 2) (\"theory::arrays::number of Ext lemmas\" 5) \
    (\"theory::strings::checkTime\" 12ms) (\"theory::arrays::theory::arrays::checkTime\" 3ms) \
    (\"theory::uf::checkTime\" 0ms) (\"smt::SolverEngine::solveTime\" 20ms) \
    (\"theory::strings::regexp::checkTime\" 7ms) \
    (\"resource::steps::inference-id\" { ARITH_UNATE: 1, STRINGS_REGISTER_TERM: 0 }) \
    (\"resource::steps::resource\" { RewriteStep: 108, TheoryCheckStep: 14 }) (\"theory::arrays::avgIndexListLength\" -nan)))"
  == { decisions := 7, lemmas := 3, theoryMs := #[("strings", 12), ("arrays", 3)],
       inferences := #[("ARITH_UNATE", 1)], rewrites := 108, theoryChecks := 14 }

/-- The sum of the timed parts of `checkSat`: the theories' checks,
preprocessing, the clausal form and theory combination. -/
def Cvc5Stats.timedMs (s : Cvc5Stats) : Nat :=
  s.theoryMs.foldl (· + ·.2) 0 + s.preprocessMs + s.cnfMs + s.combineMs

/-- The time of a `checkSat` of `checkMs` milliseconds, as Fren measures
it, that no theory's check, preprocessing, the clausal form or theory
combination accounts for, by cvc5's timers: the SAT solver's search, with
what cvc5 does around it. cvc5's own timer of the whole check,
`smt::SolverEngine::solveTime`, is 0 in cvc5 1.3.2's `checkSat`.

This takes the timers to be disjoint, which is not read from cvc5's
source. On the 6,267 queries of a check of Fren's own requirements, with
cvc5 1.3.2, no query's timed parts summed to more than its `checkSat`,
but timers that overlap in part would still meet that bound: the clausal
form of a lemma that a theory sends during its check, for one, may count
both in the theory's `checkTime` and in `cnfConversionTime`. Time counted
twice makes the rest too small. And every timer is read in whole
milliseconds, so the rest also takes in what they leave out: in a short
query, a part under a millisecond shows as 0 and goes to the rest, which
is then too large. Neither error averages out over queries, so `report`
sums the parts only over queries of `summedMs` or more, and says of a
query whose timed parts exceed its `checkSat` by how much (`overMs`),
rather than hide that in the subtraction. -/
def Cvc5Stats.searchMs (s : Cvc5Stats) (checkMs : Nat) : Nat :=
  checkMs - s.timedMs

/-- How much the timed parts exceed a `checkSat` of `checkMs`
milliseconds, which they would if two of cvc5's timers overlapped
(`searchMs`). -/
def Cvc5Stats.overMs (s : Cvc5Stats) (checkMs : Nat) : Nat := s.timedMs - checkMs

#guard ({ preprocessMs := 5, cnfMs := 4 } : Cvc5Stats).overMs 7 == 2
#guard ({ preprocessMs := 5, cnfMs := 4 } : Cvc5Stats).searchMs 7 == 0

/-- Where a `checkSat` of `checkMs` milliseconds went, largest first: each
theory's checks, the SAT search (`searchMs`), preprocessing, the clausal
form and theory combination, those that are not 0. -/
def Cvc5Stats.parts (s : Cvc5Stats) (checkMs : Nat) : Array (String × Nat) :=
  let parts := s.theoryMs ++ #[("SAT search and the rest", s.searchMs checkMs), ("preprocessing", s.preprocessMs),
    ("clausal form", s.cnfMs), ("combination", s.combineMs)]
  (parts.filter (·.2 != 0)).qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)

/-- What dominates a `checkSat` of `checkMs` milliseconds: its largest
part, if it has one. -/
def Cvc5Stats.dominant? (s : Cvc5Stats) (checkMs : Nat) : Option String := (s.parts checkMs)[0]?.map (·.1)

#guard ({ preprocessMs := 5, theoryMs := #[("datatypes", 60), ("arith", 10)] } : Cvc5Stats).dominant? 100
  == some "datatypes"
#guard ({ theoryMs := #[("strings", 20)] } : Cvc5Stats).dominant? 100 == some "SAT search and the rest"
#guard ({} : Cvc5Stats).dominant? 0 == none

/-- One query asked of the solver, with where its time went. -/
structure QueryStats where
  /-- The item whose check asked it, and the kind of that check. -/
  item : Lean.Name
  kind : Fren.Core.CheckKind
  logic : String
  /-- The size of its script, in bytes. -/
  bytes : Nat
  /-- `sat`, `unsat`, `unknown` or `error`. -/
  outcome : String
  phases : Phases
  cvc5 : Cvc5Stats
  deriving Inhabited

/-- `ns` nanoseconds in milliseconds, to a tenth. -/
def ms (ns : Nat) : String :=
  let tenths := (ns + 50000) / 100000
  s!"{tenths / 10}.{tenths % 10}"

def Phases.show (p : Phases) : String :=
  s!"setup {ms p.setup}, init {ms p.init}, assert {ms p.assert}, check {ms p.check}, model {ms p.model}, \
    free {ms p.free} ms"

/-- `(name, n)`s as `name n, …`. -/
def showCounts (xs : Array (String × Nat)) (unit : String := "") : String :=
  ", ".intercalate (xs.toList.map fun (k, n) => s!"{k} {n}{unit}")

/-- `n` bytes in kilobytes, to a tenth. -/
def kb (n : Nat) : String :=
  let tenths := (n + 50) / 100
  s!"{tenths / 10}.{tenths % 10}"

/-- Parts of a time in milliseconds, or `no timer over 0 ms` if there are
none. -/
def showParts (xs : Array (String × Nat)) : String :=
  if xs.isEmpty then "no timer over 0 ms" else showCounts xs " ms"

/-- `ns` nanoseconds in whole milliseconds, rounded. -/
def wholeMs (ns : Nat) : Nat := (ns + 500000) / 1000000

/-- The sums of `xs`'s counts, by name, largest first. -/
def sumCounts (xs : Array (String × Nat)) : Array (String × Nat) :=
  let m : Std.HashMap String Nat := xs.foldl (init := {}) fun m (k, n) => m.insert k (m.getD k 0 + n)
  m.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)

/-- The shortest `checkSat`, in milliseconds, whose parts the report sums:
in a shorter one, what cvc5's whole-millisecond timers leave out is too
large a share (`Cvc5Stats.searchMs`). -/
def summedMs : Nat := 5

/-- How many of the slowest queries the report lists unless told
otherwise (`--solver-stats=N`). -/
def listed : Nat := 20

/-- The report of `--solver-stats` (`Reqs/dev/Testing#solver-statistics`),
each line starting with `solver-stats: `: the queries' total time by
phase, then a line for each logic with its queries' time by phase, then
where their `checkSat` went by cvc5's timers, summed, and how many
queries' timed parts exceed their `checkSat`, if any did; then the `listed?`
slowest queries (all of them for `none`), each with its item, the kind of
its check, its logic, its size and its answer, a line of its phases, one
of where its `checkSat` went by cvc5's timers, one of its counts, and one
of its commonest inferences, if it made any. -/
def report (qs : Array QueryStats) (listed? : Option Nat := some listed) : String := Id.run do
  let p := "solver-stats: "
  let mut out := ""
  let all := qs.foldl (fun (acc : Phases) (q : QueryStats) => acc.add q.phases) {}
  out := out ++ s!"{p}queries asked of the solver: {qs.size}, {ms all.total} ms ({all.show})\n"
  -- By logic, for the cost of initializing its theories.
  let logics := (qs.map (·.logic)).foldl (init := #[]) fun acc l => if acc.contains l then acc else acc.push l
  for l in logics.qsort (· < ·) do
    let these := qs.filter (·.logic == l)
    let ph := these.foldl (fun (acc : Phases) (q : QueryStats) => acc.add q.phases) {}
    out := out ++ s!"{p}logic {l}, queries: {these.size}, {ms ph.total} ms ({ph.show})\n"
  -- Where `checkSat` went, by cvc5's timers, summed over the queries
  -- long enough that their timers' whole milliseconds say much
  -- (`Cvc5Stats.searchMs`).
  let long := qs.filter fun q => wholeMs q.phases.check ≥ summedMs
  let parts := sumCounts (long.flatMap fun q => q.cvc5.parts (wholeMs q.phases.check))
  let longMs := long.foldl (fun acc q => acc + q.phases.check) 0
  -- And of how many queries' the timed parts exceed their `checkSat`,
  -- listed or not (`Cvc5Stats.overMs`).
  let overs := qs.filterMap fun q =>
    let over := q.cvc5.overMs (wholeMs q.phases.check)
    if over == 0 then none else some over
  out := out ++ s!"{p}checkSat of queries of {summedMs} ms or more: {long.size}, {ms longMs} ms, by cvc5's timers: \
    {showParts parts}\n"
  -- On a line of its own, since it counts every query, not only those
  -- summed above.
  unless overs.isEmpty do
    out := out ++ s!"{p}queries of any length whose timed parts exceed their checkSat: {overs.size}, \
      by {overs.foldl (· + ·) 0} ms\n"
  let sorted := qs.qsort fun a b => a.phases.total > b.phases.total ||
    (a.phases.total == b.phases.total && Fren.Core.showPath a.item ++ " " ++ a.kind.noun < Fren.Core.showPath b.item ++ " " ++ b.kind.noun)
  let shown := listed?.getD sorted.size
  for q in sorted.extract 0 shown, i in [1:shown + 1] do
    let s := q.cvc5
    let checkMs := wholeMs q.phases.check
    let dominant := ((s.dominant? checkMs).map fun d => s!", dominated by {d}").getD ""
    out := out ++ s!"{p}{i}. {ms q.phases.total} ms: `{Fren.Core.showPath q.item}` ({q.kind.noun}), {q.logic}, {kb q.bytes} KB, {q.outcome}{dominant}\n"
    out := out ++ s!"{p}  phases: {q.phases.show}\n"
    let over := s.overMs checkMs
    let overNote := if over == 0 then "" else s!" (cvc5's timers exceed it by {over} ms)"
    out := out ++ s!"{p}  checkSat {checkMs} ms{overNote}: {showParts (s.parts checkMs)}\n"
    out := out ++ s!"{p}  counts: {s.decisions} decisions, {s.conflicts} conflicts, {s.propagations} propagations; \
      {s.theoryChecks} theory checks, {s.rewrites} rewrites, {s.lemmas} lemmas, {s.instantiations} instantiations, \
      {s.resourceUnits} resource units\n"
    let inferences := (sumCounts s.inferences).extract 0 5
    unless inferences.isEmpty do
      out := out ++ s!"{p}  inferences: {showCounts inferences}\n"
  return out

/-- A query of `a`'s expectation whose `checkSat` took
`checkMs` milliseconds, by `cvc5`'s statistics. -/
private def testQuery (checkMs : Nat) (cvc5 : Cvc5Stats) : QueryStats :=
  { item := `a, kind := .expect, logic := "ALL", bytes := 10, outcome := "unsat",
    phases := { check := checkMs * 1000000 }, cvc5 }

-- A query whose timed parts exceed its `checkSat` says so in the summed
-- line, though it is not listed.
#guard (report #[testQuery 3 { preprocessMs := 2, cnfMs := 3 }, testQuery 9 {}] (some 0)).contains
  "solver-stats: queries of any length whose timed parts exceed their checkSat: 1, by 2 ms\n"
-- The slowest query is listed first, by its total time.
#guard (report #[testQuery 3 {}, { testQuery 9 {} with item := `slow }, testQuery 5 {}] (some 1)).contains
  "solver-stats: 1. 9.0 ms: `slow` (expectation)"
#guard !(report #[testQuery 3 {}, { testQuery 9 {} with item := `slow }, testQuery 5 {}] (some 1)).contains
  "solver-stats: 2. "
-- `N` past the number of queries lists them all, and no more.
#guard (report #[testQuery 3 {}, testQuery 9 {}, testQuery 5 {}] (some 5)).contains "solver-stats: 3. "
#guard !(report #[testQuery 3 {}, testQuery 9 {}, testQuery 5 {}] (some 5)).contains "solver-stats: 4. "
-- The parts are summed over the queries of `summedMs` or more only.
#guard (report #[testQuery 3 { preprocessMs := 1 }, testQuery 9 { preprocessMs := 2 }] (some 0)).contains
  "checkSat of queries of 5 ms or more: 1, 9.0 ms, by cvc5's timers: SAT search and the rest 7 ms, preprocessing 2 ms"

end FrenCli.SolverStats
