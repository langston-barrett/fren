/-!
# The front-end fuzzer's time limit

When `fren_fuzz_frontends` stops a spec as a timeout (`testing::fuzz_overdue`,
which `Impls.Testing` proves of `overdue`).
-/

namespace FrenTest.SpecTimeout

/-- Whether a spec has run longer than `limit` seconds, leaving out the time
in solver queries that ended at their time limit: it has run for `elapsed`
milliseconds, `timedOut` of them in such queries. A query that times out
is slow by design, but a spec that runs on without one, in a loop of
Fren's own or in a query that ignores its time limit, hangs. A query
still running counts. -/
def overdue (limit elapsed timedOut : Nat) : Bool := elapsed - timedOut > limit * 1000

-- Two queries that time out in each front end, 40 s of the spec's 41 s:
-- not a hang (seed 1198158).
#guard !overdue 30 41000 40000
-- Without any, more than the limit is.
#guard overdue 30 30001 0 && !overdue 30 30000 0
-- Beyond the limit outside of the queries that timed out, however many did.
#guard overdue 30 71000 40000

end FrenTest.SpecTimeout
