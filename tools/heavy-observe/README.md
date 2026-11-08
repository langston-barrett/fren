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

Schema 2 adds `input_kind` (`file`, `stdin`, `query`, or `unknown`). The shared
Std-only parser selects one positional input and the last separated setting
of `-o/-i/-c/-b/--setup`, consuming operands even when they look like options.
`source` plus `cwd` identifies the selected disk input; stdin labels are never
disk sources. Queries have no source/setup/output fields. Canonical
`--run file` excludes subsequent program data from metadata. Selected paths
on failed invocations do not establish that bytes were consumed or produced.

The parser deliberately supports a conservative subset. Neutral `--json`,
`-q`, `--stats`, the root build's `-Dweak.fren.runChecks=false`, and separated
`-R/--root` operands are recognized. Other options, attached/other long
forms, `--` boundaries, missing operands, multiple positional files and
ambiguous run syntax produce `unknown` with no source/setup/output metadata.
Once a query or canonical run boundary is recognized, later tokens are not
compiler metadata. The raw argument list is always forwarded unchanged.
Ordinary Lake's separated settings remain fully observed.

`module_hint` is a path hint, not a parsed module name. Source content
before/after, setup and selected output-path fingerprints are partial,
non-cryptographic `lean-bytearray64:<bytes>:<hash>` values. The executable
fingerprint does not hash shared libraries. Imports, plugins, environment
and arbitrary reader inputs are not closed over. `input_closure` remains
absent and `identity_complete` false. These are never exact forecast keys.

Fingerprinting first pins the candidate with Linux `O_PATH`, then obtains
raw mode/size/device/inode with `fstat`. This identity acquisition must not
open a FIFO as a reader or release a blocked producer. The actual Lean
`fingerprintAllowed` function checks mode/size before a read-capable open.
Only an eligible pinned regular object is reopened through `/proc/self/fd`;
the reopened descriptor must retain the device/inode identity. No second
pathname lookup for reading is used. This protects against pathname
replacement without the FIFO rendezvous caused even by `O_RDONLY|O_NONBLOCK`.
The Python helper uses the same route for both candidates and copies the
validated observer bytes, without reopening its pathname for the copy.

Pipes, FIFOs, devices, directories, files over 64 MiB and incomplete reads
have absent fingerprints. The buffer bound remains 64 MiB. Procfs and OS
semantics, descriptor authenticity and concurrent content mutation remain
external assumptions; the pure eligibility theorem is not an OS proof.
All runtime fingerprint roles, including recursion-copy checks, use the
same reader. Synchronized producer-first controls verify the shared reader
and a real compiler FIFO invocation; a helper control replaces the actual
pathname after pinning and verifies the original inode's bytes are read.

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
record publication. The harness also compiles all four C definitions against the actual emitted
Main.c declarations. Old extra world parameters are incompatible even when
unused; no runtime failure or refcount bug is inferred. Metadata controls use
the pinned compiler, including repeated settings, option-shaped operands,
stdin/discovery, unsupported long/attached forms and run boundaries. This
toolchain has LLVM emission disabled; `-b` setting controls use a real run
boundary that skips emission, and make no bitcode-generation claim.
The pure test checks every 16-bit wait status against
Python's OS macros and the error/clock/identity boundaries. All signals target
owned test processes. No other compiler families or admission rollout are
included.

Requirements live in `src/Reqs/dev/Testing.md`; the actual result, elapsed,
usage, fingerprint eligibility, argument boundary and identity functions are
bound in `src/Impls/HeavyOwnership.lean`.
The proofs cover decoded pure values. Clock/fork/exec/wait4, filesystem and
signal authenticity remain external assumptions exercised by integration.
