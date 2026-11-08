# Lean compiler observations for Heavy

This opt-in Linux launcher records a real Lean compiler subprocess, without
changing admission. It is a standalone package using Lean core/Std and
`observer.c`; it imports the actual `src/Heavy/Process.lean` pure functions.
It has no Fren, solver or third-party package dependency. Invocation never
runs Lake or builds the project being observed. The installed Python Heavy
and its measured-memory backstop remain active.

From the repository root, with the pinned toolchain already installed:

```sh
scripts/heavy lake -d tools/heavy-observe build heavy_observe process_tests --wfail
scripts/heavy --offline python3 -I tools/heavy-observe/overlay.py \
  "$PWD/tools/heavy-observe/overlay" \
  --real-lean /opt/elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
scripts/heavy --offline python3 -I tools/heavy-observe/test.py
```

The setup helper requires a new destination and an explicit real compiler.
It copies the observer to `bin/lean` and records the canonical real compiler
path in `real-lean.path`. Only installed toolchain assets are delegated via
read-only-use symlinks. The overlay's configuration, executable, records and
all build caches are owned locally; no `.lake/packages` or `.git` is shared.
Never write through the delegated asset links. No shared toolchain is edited.
Python is needed for setup/tests, not for compiler invocation.

In an already prepared, dependency-local scratch package, select the overlay
using the real Lake executable (substitute absolute paths):

```sh
/path/to/repo/scripts/heavy --offline env \
  LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT=/path/to/owned/overlay \
  /opt/elan/toolchains/leanprover--lean4---v4.32.0/bin/lake build Measure
```

Lake uses `getLean` from its detected installation: a PATH shim alone does
not intercept module compilation. Discovery queries are forwarded to the
real compiler, including its real `--print-prefix`. `leanir`, C compilation
and linking are delegated, not measured by this slice. Do not use this
experimental overlay as an installed toolchain or an admission controller.

Each invocation inherits cwd, environment, arguments and standard streams.
It records the explicit compiler's version and git hash before launching,
then forks/execs that compiler and waits for that exact PID with `wait4`.
The small C boundary collects raw errors, raw Linux wait status, monotonic
nanoseconds, user/system CPU microseconds and peak RSS in KiB. It publishes
one mode-0600 `process-*.json` per invocation in `overlay/records`, or
`HEAVY_OBSERVE_DIR`. Read records after invocations finish. An abrupt observer
termination can lose a record; there is no durability or supervisor-recovery
claim. The observer adds no signal handlers for cancellation/cleanup.
Signals delivered to the child are recorded and re-raised by the observer.
A record-write or clock failure does not replace an available child outcome.
A setup failure returns 125; exec failure returns 127 and records its errno.

`source` plus `cwd` identifies the compiler input. `module_hint` is a path
hint, not a parsed Lake module name. Arguments, setup-file fingerprint,
source content before/after and requested `-o/-i/-c/-b` artifact fingerprints
are retained. Missing/ambiguous source paths stay absent. Fingerprints are
labelled `lean-bytearray64:<bytes>:<hash>`: non-cryptographic, partial content
observations. The executable fingerprint does not hash the toolchain's
shared libraries. Imports, plugins, environment and arbitrary reader inputs
are not closed over. `input_closure` is always absent and
`identity_complete` is therefore always false in this launcher. Never feed
these partial identities into an exact-key forecast as if they were complete.

Fingerprinting opens nonblocking and inspects that descriptor with `fstat`.
The actual Lean `fingerprintAllowed` function checks raw mode/size before
any bytes are read. Pipes, FIFOs, devices, directories, files over 64 MiB
and incomplete reads have absent fingerprints. This bounds the observer's
fingerprint buffer and avoids consuming a compiler's FIFO input or hanging
on piped output such as `-c /dev/stdout`. Metadata extraction stops after
the `--run` operand; following program arguments remain opaque and are
still forwarded unchanged.

Raw usage fields always accompany their error/status fields.
`measured_cpu_us` and `measured_peak_rss_kib` are absent unless an executed,
terminated child was reaped successfully. A signal-terminated compiler is a
censored measurement. Wait4's peak can include inherited pre-exec mappings
and descendants the child waited for; it is not the concurrent process-tree
peak, private memory, PSS, a reservation or a safe bound. Wall time covers
fork through wait4, excluding fingerprinting, version probes and publishing.
Measure caller wall time for total observer overhead.

The registered Linux `heavyProcess` job builds both standalone targets and
runs the harness as part of `lake test`. With the repository driver already
built, run `scripts/heavy --offline lake env .lake/build/bin/fren_test
--job heavyProcess`. Other platforms report a skip, since this first
observer is Linux-only. The manual standalone recipe
above remains independent of Fren.

The integration test retains its owned scratch directory and `report.json`
under `test-work/`. It compares a clean three-module Lake build on each side
with cache restoration disabled, including artifact SHA256, and runs bounded
warm direct-compiler pairs. It checks discovery, streams/args/environment,
ordinary errors/exits, a real Lean process's self-signal, missing executables,
record failure, recursive overlays, changed/incomplete identity and concurrent
record publication. The pure test checks every 16-bit wait status against
Python's OS macros and the error/clock/identity boundaries. All signals target
owned test processes. No other compiler families or admission rollout are
included.

Requirements live in `src/Reqs/dev/Testing.md`; the actual result, elapsed,
usage, fingerprint eligibility, argument boundary and identity functions are
bound in `src/Impls/HeavyOwnership.lean`.
The proofs cover decoded pure values. Clock/fork/exec/wait4, filesystem and
signal authenticity remain external assumptions exercised by integration.
