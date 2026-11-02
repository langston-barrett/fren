/-!
# Time in solver queries that timed out

How much wall-clock time this process has spent in solver queries that
ended at their time limit, which both front ends record. A query that
times out is slow by design, so `fren_fuzz_frontends` leaves this time out
of a spec's, and its own time limit then stops only a spec that hangs
(`Reqs/dev/Testing#fuzzer-time-limit`). Neither front end reads it, and no
check depends on it.

Queries run in parallel, in both front ends, so the time is the wall-clock
time that such queries cover, not the sum of their durations: four that
time out together in 10 s leave out 10 s, not 40 s (`Credit.step`). And
each query counts for at most its own time limit and `slackMs`, before it
ended, so that time a front end spends before the solver starts, such as
lean-smt's translation of the goal, still counts.
-/

namespace Fren.Core

/-- The time left out so far, in milliseconds of the monotonic clock
(`testing::solver_credit`). -/
structure Credit where
  /-- The time left out. -/
  credit : Nat := 0
  /-- The latest end of a query left out, before which no time is left out
  again. -/
  covered : Nat := 0
  deriving Inhabited, Repr, BEq

/-- `c` after a query that timed out over `[start, stop]`: only the part
after `c.covered` is left out. Each part left out is thus within its query
and after every part left out before, whatever order the queries end in,
so the time left out is at most the length of the union of the queries. -/
def Credit.step (c : Credit) (start stop : Nat) : Credit :=
  { credit := c.credit + (stop - max start c.covered), covered := max c.covered stop }

-- Four queries that time out together, in any order, leave out 10 s.
#guard ([(0, 10000), (5, 10000), (2, 9998), (1, 10001)].foldl (fun (c : Credit) (a, b) => c.step a b) {}).credit == 10001
-- Queries one after another leave out each one's time.
#guard (((({} : Credit).step 0 10000).step 10000 20000).step 25000 35000).credit == 30000

/-- How long after its time limit a query that timed out may still be left
out, for the solver to stop and answer. -/
def slackMs : Nat := 1000

/-- The time left out of this process's solver queries that ended at their
time limit. -/
initialize solverCredit : IO.Ref Credit ← IO.mkRef {}

/-- The milliseconds left out so far (`solverCredit`). -/
def solverTimeoutMs : BaseIO Nat := return (← solverCredit.get).credit

/-- Whether the solver's explanation of an `unknown` answer, as cvc5 gives
it, says that the query reached its time limit. -/
def timedOutExplanation (explanation : String) : Bool := explanation == "TIMEOUT"

#guard timedOutExplanation "TIMEOUT" && !timedOutExplanation "INCOMPLETE" && !timedOutExplanation "RESOURCEOUT"

/-- Runs a solver query whose time limit is `limitSecs` (0 for none), and,
if it ended at that limit (`timedOut`), leaves out its time
(`solverCredit`): at most `limitSecs` seconds and `slackMs` before it
ended. -/
def timeQuery {m : Type → Type} {α : Type} [Monad m] [MonadLiftT BaseIO m] (limitSecs : Nat) (timedOut : α → Bool)
    (query : m α) : m α := do
  let start ← (IO.monoMsNow : BaseIO Nat)
  let r ← query
  if timedOut r then
    let stop ← (IO.monoMsNow : BaseIO Nat)
    let start := if limitSecs == 0 then start else max start (stop - (limitSecs * 1000 + slackMs))
    (solverCredit.modify (·.step start stop) : BaseIO Unit)
  return r

end Fren.Core
