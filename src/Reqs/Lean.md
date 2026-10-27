# Lean embedding

In Lean, a spec is part of a Lean file. Fren's syntax is enabled by `open
Fren.Lang`, and only in the file (or section) where it is opened, so Fren's
keywords do not affect other Lean code.

```lean
import Fren
open Fren.Lang

mod climate

pub proc thermostat() { ... }

#fren_check
```

## Libraries

| Import | Provides |
|---|---|
| `Fren` | everything below |
| `Fren.Spec` | the language and its [generated declarations](Generated.md), without the checker or the solver |

Lean code that only uses a spec's types and definitions can import the spec
from a file that imports only `Fren.Spec`. Checking and implementations
need `Fren`.

## Commands

| Command | Meaning |
|---|---|
| `#fren_check` | runs the [checks](Check.md) on every procedure and global expectation declared earlier in the current Lean file |
| `#fren_check p` | runs the checks on `p` only; `p` must name a procedure or a global expectation |
| `#fren_md "file.md"` | reads a [Markdown spec](Markdown.md) |
| `impl` | states and proves that Lean code meets a procedure (see [Implementations](Impl.md)) |
| `interp` | gives the Lean meaning of an abstract type or a function (see [Interpretations](Impl.md#interpretations)) |
| `tested`, `trusted` | claim evidence for a procedure (see [Traceability](Trace.md)) |
| `#fren_trace` | reports the evidence for every procedure (see [Traceability](Trace.md)) |

A procedure or global expectation is checked only where a `#fren_check`
follows it, in the same Lean file, and only if no static error comes
before the `#fren_check` (see [Static errors](View.md#static-errors)). The results are reported as Lean messages (see
[Diagnostics](View.md)), so a failing check fails `lake build`.

## Options

Set with `set_option`:

| Option | Type | Default | Effect |
|---|---|---|---|
| `fren.timeout` | `Nat` | `10` | time limit in seconds for each solver query; 0 means none |
| `fren.resourceLimit` | `Nat` | `0` | limit on the solver's work for each query, in cvc5's resource units; 0 means none (see [Limits](Cli.md#limits)) |
| `fren.examples` | `Nat` | `1` | the most notes of [forced outputs](Check.md#forced-outputs) shown for each unrealizable procedure, as `fren check --examples` (see [Forced outputs](Cli.md#forced-outputs)); there is no `all`, but a number at least the number of guarantees shows them all |
| `fren.requireEvidence` | `String` | `""` | warn about procedures with weaker evidence than this (see [Traceability](Trace.md)) |
| `fren.testGlobs` | `String` | `""` | space-separated globs of tests that `#fren_trace` scans for `fren-covers:` markers (see [Traceability](Trace.md)) |
| `fren.lint.LINT` | `String` | the lint's | the level of the [lint](Lint.md) `LINT`: `"allow"`, `"expect"`, `"warn"`, `"deny"` or `"forbid"` |

The `fren.lint` options follow the rules of [Setting
levels](Lint.md#setting-levels): options set outside the file, such as a
Lake package's `leanOptions`, are the command line, and a forbidden lint
cannot be set to another level later in the file.

## Files

A Lean file sees the Fren modules and items of the Lean files it imports,
and starts in the root module (see [Modules and
visibility](Lang/Modules.md#across-files)). Fren modules are independent of
Lean namespaces, but the [generated declarations](Generated.md) are placed
in `Fren.Generated`, under the current Lean namespace, which `open
Fren.Lang` opens (see [Names](Generated.md#names)).
