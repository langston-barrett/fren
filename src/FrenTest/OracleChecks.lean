-- keep-sorted start
import FrenTest.Conformance
import FrenTest.Coverage
-- keep-sorted end

/-! # Regression tests of the oracle verdict paths

The `oracleGuards` job runs these as compiled code, including negative
controls for a method's empty comparisons, unread counters, a failed tool
with usable output, and internal errors beside a normal summary.
-/

namespace FrenTest.OracleChecks

def check : Array String := Id.run do
  let mut fs := #[]
  let require (ok : Bool) (what : String) := if ok then #[] else #[what]
  fs := fs ++ require (!(Oracle.finish "enumeration" 0 500 #[]).isEmpty &&
    !(Oracle.finish "enumeration" 499 500 #[]).isEmpty &&
    (Oracle.finish "enumeration" 500 500 #[]).isEmpty &&
    !(Oracle.finish "enumeration" 500 500 #["internal error: injected"]).isEmpty &&
    !(Oracle.finish "enumeration" 500 0 #[]).isEmpty) "enumeration: vacuous agreement or prior failure accepted"
  fs := fs ++ require (!(Coverage.inputFailures 0 0).isEmpty &&
    !(Coverage.inputFailures 1 0).isEmpty && !(Coverage.inputFailures 0 1).isEmpty &&
    (Coverage.inputFailures 1 1).isEmpty) "coverage: empty modules or run counters accepted"
  let gcov := "Function 'f'\nLines executed:100.00% of 1\n"
  fs := fs ++ require ((Oracle.toolFailures gcov "" 0).isEmpty &&
    !(Oracle.toolFailures gcov "" 1).isEmpty && !(Oracle.toolFailures "" "warning: injected" 0).isEmpty &&
    !(Oracle.toolFailures (gcov ++ "internal error: injected") "" 0).isEmpty &&
    !(Oracle.toolFailures gcov "internal error: injected" 0).isEmpty)
    "coverage: failed, empty or internally errored counter reader accepted"
  let summary := "fren: 1 passed, 0 failed, 0 inconclusive, 0 redundant"
  fs := fs ++ require ((Conformance.failures summary 0).isEmpty &&
    !(Conformance.failures "fren: 0 passed, 0 failed, 0 inconclusive, 0 redundant" 0).isEmpty &&
    !(Conformance.failures ("internal error: injected\n" ++ summary) 0).isEmpty &&
    !(Conformance.failures ("error: internal error: injected\n" ++ summary) 1).isEmpty &&
    !(Conformance.failures summary 1).isEmpty && !(Conformance.failures summary 2).isEmpty &&
    !(Conformance.failures summary 3).isEmpty && !(Conformance.failures summary 137).isEmpty &&
    !(Conformance.failures "" 0).isEmpty) "conformance: empty checks, internal error or unexplained exit accepted"
  fs := fs ++ require (!(Conformance.failures "fren: 1 passed, junk failed, 0 inconclusive, 0 redundant" 0).isEmpty &&
    !(Conformance.failures "fren: 1 passed, 0 failed, 1 inconclusive, 0 redundant" 0).isEmpty &&
    !(Conformance.failures "fren: 1 passed, 0 failed, 10 inconclusive, 0 redundant" 0).isEmpty &&
    !(Conformance.failures ("error: could not check\n" ++ summary) 1).isEmpty)
    "conformance: malformed summary, inconclusive count or static error accepted"
  fs := fs ++ require ((Conformance.failures
    "warning[F0664]: premise did not pass\nfren: 1 passed, 0 failed, 1 inconclusive, 0 redundant" 3).isEmpty &&
    (Conformance.failures "error[F0600]: check failed\nfren: 0 passed, 1 failed, 0 inconclusive, 0 redundant" 1).isEmpty)
    "conformance: an explained checking exit was rejected"
  return fs

#guard check.isEmpty

end FrenTest.OracleChecks
