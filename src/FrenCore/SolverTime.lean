/-!
# Time in solver queries that timed out

How long this process has spent in solver queries that ended at their
time limit, which both front ends record. A query that times out is slow
by design, so `fren_fuzz_frontends` leaves this time out of a spec's, and
its own time limit then stops only a spec that hangs (`Reqs/dev/Testing`).
Neither front end reads it, and no check depends on it.
-/

namespace Fren.Core

/-- The milliseconds that this process has spent in solver queries that
ended at their time limit. -/
initialize solverTimeoutMs : IO.Ref Nat ← IO.mkRef 0

/-- Whether the solver's explanation of an `unknown` answer, as cvc5 gives
it, says that the query reached its time limit. -/
def timedOutExplanation (explanation : String) : Bool := explanation == "TIMEOUT"

#guard timedOutExplanation "TIMEOUT" && !timedOutExplanation "INCOMPLETE" && !timedOutExplanation "RESOURCEOUT"

/-- Runs a solver query, and adds its time to `solverTimeoutMs` if it ended
at its time limit (`timedOut`). -/
def timeQuery {m : Type → Type} {α : Type} [Monad m] [MonadLiftT BaseIO m] (timedOut : α → Bool) (query : m α) :
    m α := do
  let start ← (IO.monoMsNow : BaseIO Nat)
  let r ← query
  if timedOut r then
    let stop ← (IO.monoMsNow : BaseIO Nat)
    (solverTimeoutMs.modify (· + (stop - start)) : BaseIO Unit)
  return r

end Fren.Core
