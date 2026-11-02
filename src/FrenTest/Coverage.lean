/-!
# What `fren_coverage` makes of a declaration

Whether a counted declaration that the tests did not run fails the
coverage, and whether its line in `test/coverage.txt` is stale
(`testing::coverage`, which `Impls.Testing` proves of `fails` and
`stale`). The facts are gcov's and the compiled code's: whether one of its
entry points ran, and whether a compiled entry point reaches it
(`FrenCoverage`).
-/

namespace FrenTest.Coverage

/-- A counted declaration fails the coverage if no test ran it, a compiled
entry point reaches it, and `test/coverage.txt` does not list it. One that
none reaches is used only by proofs and by what Lean interprets while a
module builds, such as `#guard`s and `#eval`s, and runs in no executable,
so no test could run it. -/
def fails (ran reached listed : Bool) : Bool := !ran && reached && !listed

/-- A listed declaration's line is stale if a test ran it, or no compiled
entry point reaches it: either way the line is not needed. -/
def stale (ran reached listed : Bool) : Bool := listed && (ran || !reached)

-- A function that only proofs use is not a gap, listed or not.
#guard !fails false false false
-- A compiled one that no test runs is, until it is listed.
#guard fails false true false && !fails false true true
#guard stale false false true && stale true true true && !stale false true true

end FrenTest.Coverage
