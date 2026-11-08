# Lean compiler observations for Heavy

This opt-in Linux launcher records a real Lean compiler subprocess. With no
budget configuration it preserves the original observe-only behavior. It is a standalone package using Lean core/Std and
`observer.c`; it imports the actual `src/Heavy/Process.lean` pure functions.
It has no Fren, solver or third-party package dependency. Invocation never
runs Lake or builds the project being observed. The installed Python Heavy
and its measured-memory backstop remain active.

From the repository root, with the pinned toolchain already installed:

```sh
scripts/heavy lake -d tools/heavy-observe build heavy_observe process_tests budget_session budget_tests --wfail
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
experimental overlay as an installed toolchain. The optional development
controller below admits compiler children within one build.

Each invocation inherits cwd, environment, arguments and standard streams.
It records the explicit compiler's version and git hash before launching,
then forks/execs that compiler and waits for that exact PID with `wait4`.
The small C boundary collects raw errors, raw Linux wait status, monotonic
nanoseconds, user/system CPU microseconds and peak RSS in KiB. It publishes
one mode-0600 `process-*.json` per invocation in `overlay/records`, or
`HEAVY_OBSERVE_DIR`. Read records after invocations finish. An abrupt observer
termination can lose a record; there is no durability or supervisor-recovery
claim. The observe-only path adds no signal handlers for cancellation/cleanup.
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

The registered Linux `heavyProcess` job builds the standalone targets and
runs the harness as part of `lake test`. With the repository driver already
built, run `scripts/heavy --offline lake env .lake/build/bin/fren_test
--job heavyProcess`. Other platforms report a skip, since this first
observer is Linux-only. The manual standalone recipe
above remains independent of Fren.

The integration test retains its owned scratch directory and `report.json`
under `test-work/`. It compares a clean ordinary and budget-controlled three-module Lake build
with cache restoration disabled, including artifact SHA256, and runs bounded
warm direct-compiler pairs. It checks discovery, streams/args/environment,
ordinary errors/exits, a real Lean process's self-signal, missing executables,
record failure, recursive overlays, changed/incomplete identity and concurrent
record publication. The harness also compiles all six C definitions against the actual emitted
Main.c and BudgetMain.c declarations. Old extra world parameters are incompatible even when
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


## One-build compiler reservations

`budget_session` owns one new mode-0700 directory and one controlled build
process group. It is a transient parent, not a service or machine scheduler.
Use an absolute directory under an owned temporary build directory; it must
not exist. An example with explicitly selected development values follows:

```sh
/path/to/repo/scripts/heavy --offline env \
  LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT=/path/to/owned/overlay \
  /path/to/budget_session /path/to/owned/build/session \
  1300000 100000 1200000 5000 /path/to/owned/requests -- \
  /opt/elan/toolchains/leanprover--lean4---v4.32.0/bin/lake build Measure
```

Arguments are session directory, total allowance in KiB, parent headroom in
KiB, unknown-request fallback in KiB, admission timeout in milliseconds,
request manifest, `--`, absolute command and its arguments. The example
leaves 1200000 KiB for compiler reservations. Parent headroom is subtracted
once. It covers Lake, wrappers and the existing pre-admission version/hash
discovery probes; those probes are not separately charged compiler requests.
The allowance is therefore reservation accounting, not a bound on their RAM.
The outer Heavy/fd reservation and cgroup are unchanged; these inner
charges are not added to its forecast. No CPU weights, affinity, tokens,
installation defaults or cross-build admission change.

The manifest has one tab-separated absolute canonical source path,
`lean-bytearray64:<bytes>:<hash>` fingerprint and positive KiB demand per
line. Use `process_tests --read PATH` to obtain the same ByteArray hash as
the observer; prefix its `some:HASH` result with the source byte count as
above. A match selects the explicit request; unsupported, absent or changed
metadata uses the explicit positive fallback. Malformed and duplicate rows
fail configuration. The caller supplies both requests and fallback. Neither
is calibrated or a safe upper bound merely because it is positive. These
source-bound requests are configuration, not measured peaks or exact-key
forecasts: dependencies, plugins and environment closure remain incomplete.

The gate freezes the selected demand, publishes an increasing waiting
ticket, and holds one registry lock while reading locked leases, calling
the actual Std-only ownership/charge/fit functions and publishing running
state. Only the oldest held waiter may start; after it starts, another
fitting request may start too. There is no concurrency cap. Intrinsically
oversized requests fail promptly. Lock contention and capacity waits retry
until the fixed caller deadline. Read, lock and write failures fail closed.
A held malformed or independently mismatched owner fails the snapshot;
unlocked residual metadata contributes nothing. Reservations do not age.

Every held row has PID, start counter, boot ID and PID namespace identity.
The gate checks its session owner's lock and independently reads its raw
identity on every snapshot. It rejects ancestor-mounted procfs and callers
outside the owned process group. It never takes over a session or signals
a ledger PID. The compiler inherits its own lease descriptor across exec;
the observer closes only that descriptor after wait4. A surviving inherited
holder cannot silently become a zero charge when its monitor disappears.

In this controlled Linux envelope, parent-death SIGKILL propagates through
the command, observer and compiler. INT/TERM/HUP cancellation during gated
execution first terminates the observer's own unreaped child, then escalates
after about 250 ms; a failed reap stops waiting after about 1.25 seconds.
The session parent pins its group ID with its unreaped command leader,
terminates that group on completion/cancellation and checks for inherited
leases. Reap and lease cleanup each have a one-second bound. A stuck task
or retained lease returns a cleanup error and leaves a retired directory.
Session directories are deliberately retained for inspection and cannot
be reused. Abrupt owner death can lose records and leave residual files;
there is no durable recovery or takeover. Commands that escape the process
group, change parent-death semantics or close inherited leases are outside
this controlled compiler boundary. Same-user hostile mutation and Linux
syscall/procfs/FFI authenticity are external assumptions, not pure proofs.

Gated records use schema 3. Requested reservation, held charge, allowance,
parent headroom, ticket, grant timestamp and admission wait are separate
from fork-to-wait child wall/CPU/wait4 RSS. `gate_errno` and `wrapper_code`
report control errors independently of a physical child outcome. Without a
child, `child_present` is false, result/usage/wall fields are absent/null,
and raw zero slots do not assert a successful child. Charge/grant fields
are meaningful as admitted snapshots only when `gate_errno` is zero; a zero
raw charge slot on a failed snapshot never means an unknown holder was free. Pre-gate configuration
errors return 125 with a diagnostic and may have no record. Abrupt death
may also leave no record. Failure of the child's parent-death setup is an observer launch error, with
its physical wait status retained and measured usage absent. A completed
cancelled child retains its raw wait
status even when the wrapper returns 125. Observe-only schema 2 is unchanged.

This allowance bounds known reservation charges at locked snapshots. It
cannot bound actual RAM, private/PSS or concurrent process-tree RSS. The
existing Python observed-memory/kill-newest backstop remains the runtime
safety layer. All children inherit the parent's priority and cgroup.

The separate bounded `heavyBudget` test job runs real deterministic
producers against actual shared locks/tickets, including unequal overlap,
FIFO, cancellation, inherited holders, owner death, unknown/PID-reused/raw
stale rows, partial publication, oversized requests and injected counter
write failure. The same producers with the actual gate bypassed demonstrate
the non-fitting overlap violation. `budget_tests` checks raw arithmetic,
owner and request boundaries. `heavyProcess` retains the existing raw-status,
FIFO, parser and ABI controls, and its one three-module Lake comparison
requires admission records plus equal streams, status and artifact bytes.
Its synthetic demands establish controller behavior, not performance or
memory-calibration evidence. Warm direct pairs still measure observe-only
cost. Requirements/impls bind the actual row charge and budget decisions;
the arithmetic theorem applies only to completed registry-locked snapshots.

## Deadline and waitable-owner checks

The admission timeout uses raw monotonic nanoseconds and one fixed deadline.
The actual Std-only deadline function checks samples before and after registry
acquisition, before publishing a running row, and after publication while the
registry is still held. An expired sample returns timeout before any compiler
launch. Waiting does not replace the ticket or extend the deadline. This is
checked eligibility at those boundaries; preemption after a successful check
can delay the eventual fork, so there is no hard real-time launch guarantee.

Before either a session command or gated compiler is forked, the controller
reads SIGCHLD disposition. This narrow Linux policy accepts only SIG_DFL
without SA_NOCLDWAIT (supported raw bit value 2). Explicit SIG_IGN, custom
handlers, automatic reaping, an unsupported bit ABI or a failed query return
125 before fork. The controller does not change SIGCHLD, so no normalization
or restoration is needed and the supported disposition is inherited normally.
INT/TERM/HUP save/rollback/restore behavior is unchanged.

Each session group signal independently obtains raw waitid WNOWAIT and
sigaction observations and calls the shared lifecycle function. A previous
wait error, a current error, another observed PID, a recorded reap or an
unsupported disposition forbids the signal. An ECHILD monitor result cannot
be erased by a later probe. TERM and KILL both require eligibility; no numeric
group signal occurs after an error loses the anchor. This relies on the
controlled process having no unrelated thread/handler reaping its children
or changing SIGCHLD between checks. OS identity, wait and signal authenticity
remain external assumptions, not a pure proof of Linux atomicity.

`heavyBudgetBoundaries` runs synchronized late-lock initial/reacquisition,
snapshot-crossing and running-publication-crossing deadline controls, plus a
timely admission. It exercises actual inherited SIGCHLD=SIG_IGN, actual
SA_NOCLDWAIT/custom dispositions, a real owned-child reap, query failures
and ordinary child statuses. The test interposer suppresses all numeric
group signals in its harmless true-child probes, recording raw wait results
before delivery; it never forces PID reuse or signals a foreign group.
The old 9e83 binaries fail those safety assertions. The ordinary 24-case
`heavyBudget` job retains real cancellation, inherited-holder and owner-death
cleanup without this signal suppression. `fren_test --job heavyProcess controls`
runs the existing real compiler, FIFO, raw parser/status and emitted C ABI
controls without repeating the historical three-module Lake comparison.


Failed source canonicalization supplies absent identity and fingerprint to
request selection. It still validates the whole manifest and uses the
configured positive fallback; original compiler arguments remain unchanged.
The actual compiler diagnoses missing, non-directory, cyclic or inaccessible
source paths. `heavyMissingSource` compares ordinary, observe-only and gated
status/stdout/stderr with the pinned compiler, requiring a real fallback
reservation/record, and separately preserves malformed-manifest rejection.
The bound normalization rule states optional-input handling; filesystem
exception authenticity and forwarding remain an actual finite IO contract,
not a pure proof of filesystem behavior or input closure.


The missing-source harness uses the active repository-selected compiler from
`lean --print-prefix`, or explicit `HEAVY_TEST_REAL_LEAN`, and canonicalizes
that executable once for hashing, overlay configuration, direct invocations
and record checks. It does not assume an installation directory or install
a toolchain. Run from the repository with its pinned toolchain available.
The registered `heavyMissingSource` job runs the same four controls through
both discovery routes using an owned temporary copy of that exact compiler.
Its bytes, version and git hash must match; installed assets are delegated
read-only in use, with no package/cache copy. The actual reported executable
must be the selected copy. These finite IO checks establish caller selection,
not a pure filesystem or dependency-closure proof.

## Developer entrypoint

With `heavy_observe` and `budget_session` already built for this checkout,
`scripts/heavy-lean-build` creates a new owned overlay and session, then
executes the existing session controller. It does not build tools or packages.
Choose the actual installed toolchain's absolute `bin/lean` explicitly; the
existing overlay helper verifies that it is the installation's compiler and
rejects a recursive observer. Supply a new absolute state directory whose
parent exists, and an absolute request manifest. For example, under the
existing fd job and Heavy offline envelope:

```sh
scripts/heavy --offline scripts/heavy-lean-build \
  --state /absolute/owned/new-state \
  --real-lean /absolute/toolchain/bin/lean \
  --allowance-kib 1300000 --headroom-kib 100000 \
  --fallback-kib 600000 --timeout-ms 30000 \
  --requests /absolute/owned/requests.tsv -- \
  /absolute/toolchain/bin/lake --no-cache --verbose build +FrenSexp.Codec
```

All values are explicit development accounting inputs, not memory guarantees.
The entrypoint passes the command after `--` as argv without shell reparsing,
keeps the inherited environment except for `LAKE_OVERRIDE_LEAN`, `LEAN_SYSROOT`
and `HEAVY_OBSERVE_DIR`, and replaces itself with `budget_session`. Records are
in `new-state/overlay/records`; the retained session is `new-state/session`.
It neither chooses a cache policy nor verifies dependency checkouts. Before
using Lake offline, verify the pinned dependency URLs and revisions and choose
an appropriate owned cache if needed; an offline Lake invocation can still
reconcile local package directories. A cached target may perform no compilation.
No default admission, forecast, installation or machine-wide configuration is
changed. If tools are missing, build the standalone targets using the documented
recipe first; the caller must ensure those prebuilt binaries match this source.
The focused standalone test is `python3 -I tools/heavy-observe/entrypoint_test.py`
through `scripts/heavy --offline`; it is also included in `test.py`.

## Compiler forecast adviser

Build the separate `compiler_advice` target with the pinned standalone
package. It reads one JSON request file, captures current identity in its
actual cwd, and prints one JSON advice object. For example:

```json
{"real_compiler":"/absolute/toolchain/bin/lean","args":["Tiny.lean","--setup","setup.json"],"cutoff_monotonic_ns":123456000000,"recent_count":20,"minimum_samples":3,"records":["/absolute/owned/process-1.json","/absolute/owned/process-2.json"]}
```

The cutoff is an explicit CLOCK_MONOTONIC nanosecond value in the current
Linux boot, never a wall-clock timestamp. The executable obtains current
monotonic now and boot identity itself. The observer adds best-effort
optional `boot_id` to schema 2/3; inability to read it does not change child
status. Records without that identity remain unknown; no completion time is
inferred from file mtime. Read completed, trusted observer files, listing
each invocation once. File authenticity and Linux clock/filesystem behavior
are external assumptions, not kernel proofs.

The Std-only `Heavy.CompilerForecast` kernel filters exact raw source/cwd,
source content, compiler path/content/version/git hash, ordered argv and
setup cohorts, then retains at most the requested recent count (maximum
1024 at the executable boundary). It selects successful, stable-source,
positive physical wait4 observations in the same boot/window and returns
their exact maximum plus count if the explicit positive minimum is met.
Malformed records are rejected and counted; missing current identity or
insufficient usable evidence returns `unknown` with a null peak. This is a
sample count, not a claim of independent observations or calibration.
Current identity is recaptured after reading history; no subsequent
stale-safe use is guaranteed. A setup fingerprint is the producer's
before-run observation; it does not prove setup stability during that run.

This statistical advice does not change complete-input provenance:
`identity_complete` remains false. Imports, environment, plugins and
libraries remain outside the partial noncryptographic identity. The peak
is neither concurrent physical RAM nor a guaranteed future bound. There
is no automatic capture, history database, gate injection, headroom or
fallback policy. Callers still supply manual requests and positive fallback
to the existing controller API.

The existing standalone integration harness runs `forecast_test.py` with
one tiny actual observed compilation and bounded raw JSON mutations through
the executable/decoder/kernel. Run that focused check alone after building
`compiler_advice heavy_observe`, under Heavy offline. `--output` selects a
new absolute owned directory for its records, requests, advice and timing.
