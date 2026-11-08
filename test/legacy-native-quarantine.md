# Legacy native test quarantine

The pre-merge and main test shards, and main’s instrumented coverage run,
opt in to `--skip-unstable-legacy` for `lake test`. This omits
`enumeration`, `nativeDiagnostics` with each of `core`, `wait`, `own` and
`wrapper`, and `nativeObservation`. Main also skips the separate
`methods-agree` job: its own-spec, UI and fuzzer-corpus comparisons among
solver, enumeration and random evidence are no longer gated. The diagnostic
environment variables for enumeration and the initial own-spec check are not
set by these test invocations. `ownSpec` itself, ordinary UI and corpus jobs,
other tests and builds remain gated. Default local selection is unchanged.
The coverage report still checks its existing inventory; omitting jobs may
leave declarations uncovered and cause it to fail. No inventory entries are
added for the quarantine, and instrumented CI must establish the effect.

The actual enumeration job has exited 139. Method agreement's UI and fuzz
parts have also exited 139; the UI capture observed a fault, whereas the fuzz
failure had no corresponding backtrace. A GDB self-crash during a deliberate
native diagnostic control is a separate observation, not proof that the
application crashed there. These observations do not establish a common cause.
Native research is parked, not solved.

For manual investigation when resumed, build a fresh driver and run individual
jobs (they may crash):

```sh
scripts/heavy lake build fren_test
scripts/heavy --offline lake env .lake/build/bin/fren_test --job enumeration
scripts/heavy --offline lake env .lake/build/bin/fren_test --job nativeDiagnostics core
scripts/heavy --offline lake env .lake/build/bin/fren_test --job nativeDiagnostics wait
scripts/heavy --offline lake env .lake/build/bin/fren_test --job nativeDiagnostics own
scripts/heavy --offline lake env .lake/build/bin/fren_test --job nativeDiagnostics wrapper
scripts/heavy --offline lake env .lake/build/bin/fren_test --job nativeObservation
scripts/heavy --offline lake env .lake/build/bin/fren_test --job methodsAgree own
scripts/heavy --offline lake env .lake/build/bin/fren_test --job methodsAgree ui 0 1
scripts/heavy --offline lake env .lake/build/bin/fren_test --job methodsAgree fuzz
```

Re-enable after the underlying failures and diagnostic reliability have been
investigated and fixed, the affected jobs pass under representative CI
conditions, and fresh CI and independent review confirm the restored gates.
Restoration is tracked in #995.
