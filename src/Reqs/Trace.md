# Traceability

Traceability relates each procedure of a spec to evidence that the system
satisfies the procedure's guarantees. Fren recognizes four kinds of
evidence:

- an [implementation](Impl.md) proved in Lean, with a written proof or by
  `decide`;
- an implementation proved by the solver;
- a `tested` claim, which names test files that exercise the procedure;
- a `trusted` claim, which records why the procedure holds without a proof
  or a test.

An implementation that holds only because no values satisfy its
procedure's assumptions is not evidence (see [Vacuous
implementations](Impl.md#vacuous-implementations)).

Implementations exist only in Lean, so they apply only to code written in
Lean. Claims are ordinary Fren items, accepted in `.fren` files, in
[Markdown specs](Markdown.md) and in Lean, and refer to tests in any
language. For a system not written in Lean, they are the only evidence.

Only procedures have evidence. A [global expectation](Lang/Global.md)
constrains nothing, so there is nothing for the system to satisfy: the
checks confirm it. Nor do a procedure's expectations and [cover
goals](Lang/Procedures.md#cover-goals) add anything for the system to
satisfy: evidence is about the assumptions and guarantees, and a cover
goal's witness, shown by `fren check`, is evidence that the spec allows a
scenario, not that the system does. Nor do [abstract types](Lang/Types.md#abstract-types) and
[functions](Lang/Items.md#functions), which constrain nothing either: their
meaning is given by an [interpretation](Impl.md#interpretations). The
checks of the [tables](Lang/Expressions.md#tables) and `match`es in a defined function's
body or a constant's value confirm how they are written, which is no
evidence about a system either.

`fren trace` reports the evidence for every procedure of the spec in the
given files; in Lean, `#fren_trace` does the same. For example, with this
spec in `thermostat.fren`:

```
proc sensor(raw: Int): (reading: Int) { ensure r: reading = raw }
proc heater(cold?): (on?) { ensure r: on? iff cold? }
proc unit(raw: Int) { call s := sensor(raw) call h := heater(s.reading < 18) }
proc display(reading: Int): (shown: Int) { ensure r: shown = reading }

tested sensor: "tests/test_sensor.py"
trusted heater: "the relay is wired so that it closes exactly when the input is high"
```

and a test `tests/test_sensor.py` containing the line
`# fren-covers: sensor`, `fren trace --tests 'tests/**/*.py' thermostat.fren`
prints:

```
evidence: 0 proved, 0 solver, 1 tested, 2 trusted, 1 missing
tested: `sensor`
trusted: `heater`, `unit`
missing: `display`
```

`unit` has no outputs, so it takes the level of its weakest call,
`heater` (see [Levels](#levels)). `display` has no evidence.

## Claims

```
claim := "tested" path ":" STRING ("," STRING)* [","]
       | "trusted" path ":" STRING
```

`tested c: "file", ...` claims that each named file tests procedure `c`.
Fren checks that each file exists and contains a marker for `c`: the text
`fren-covers:` followed by a comma-separated list of procedure paths that
includes `c`. The list runs to the end of the line, or to a `*/` that ends
it. Fren ignores what precedes the marker, so the marker can follow any
comment syntax:

```python
# fren-covers: cli::accepts
```

```c
/* fren-covers: sensor, heater */
```

A claim whose file is missing, or does not name the procedure, is an
error. A test that is deleted, or that stops naming the procedure, therefore
cannot leave a claim behind. Fren does not run the tests, and does not
measure how thoroughly they exercise the procedure.

`trusted c: "justification"` records why procedure `c` holds without a
proof or a test, such as a property of a compiler, the operating system or
the hardware. The justification cannot be blank: empty, or only
whitespace. Fren does not check it otherwise.

A procedure can have several claims. A claim does not change any check of
the procedure. Paths are relative to the current directory, which under
Lake is the package root.

## Scanning tests

Scanning tests checks the converse of a `tested` claim: that each marker in
a test is matched by a claim. `fren trace --tests GLOB`, or
`set_option fren.testGlobs "GLOB ..."` for `#fren_trace`, scans the files
that match the globs. Each marker in them must name a procedure that has a
`tested` claim naming that file; any other marker is an error, at the
marker. In a glob, `*` matches within a path segment and `**` matches any
number of segments.

Fren itself is traced in this way. Its build runs `#fren_trace` with
`fren.requireEvidence` set to `trusted` and its tests scanned, so that with
`--wfail` the build fails if a procedure of this manual has no evidence or
a marker in its tests is unclaimed.

```fren
pub mod trace

use view::Severity
use view::Severity::{Silent, Warning}
```

## Levels

Fren orders evidence into levels, from weakest to strongest:

| Level | Evidence |
|---|---|
| `missing` | none |
| `trusted` | a `trusted` claim |
| `tested` | a `tested` claim |
| `solver` | an implementation that the solver proved, added as an axiom |
| `proved` | an implementation that Lean proved |

`--require` and `fren.requireEvidence` take these names.

```fren
pub enum Level { Missing, Trusted, Tested, Solver, Proved }

use self::Level::{Missing, Proved, Solver, Tested, Trusted}
```

`trace::rank` gives the order of the levels.

```fren
pub proc rank(level: Level): (r: Int) {
    ensure order: r = if level = Missing then 0 else if level = Trusted then 1
        else if level = Tested then 2 else if level = Solver then 3 else 4

    expect proved_is_strongest: when level != Proved, r < 4
}
```

`trace::direct` gives a procedure's own evidence: the strongest of its
implementations and claims.

```fren
pub proc direct(
    proved?,             -- an `impl` proved by Lean, with a written proof or `decide`
    solver?,             -- an `impl` proved by the solver, an axiom
    tested?,             -- a `tested` claim
    trusted?,            -- a `trusted` claim
): (level: Level) {
    ensure strongest: level = if proved? then Proved else if solver? then Solver
        else if tested? then Tested else if trusted? then Trusted else Missing

    expect missing_means_none: when level = Missing,
        not proved? and not solver? and not tested? and not trusted?
}
```

A procedure without outputs computes nothing itself: it only connects its
calls and states expectations about them. Its level is therefore that of
its weakest call, or its own evidence if that is stronger; with no
calls, it is `proved`. A procedure with outputs has only its own level,
since its calls say nothing about how its outputs are computed.
`trace::evidence` gives the level that is reported.

```fren
pub proc evidence(
    own: Level,          -- the procedure's own evidence (`direct`)
    has_outputs?,
    weakest: Level,      -- the weakest evidence among its calls; `Proved` if it has none
): (level: Level) {
    call o := rank(own)
    call w := rank(weakest)

    ensure derived: level = if has_outputs? or o.r >= w.r then own else weakest

    expect outputs_need_own: when has_outputs?, level = own
    expect never_weaker: when level != own, not has_outputs?
}
```

Evidence only adds up: having more of it never lowers a procedure's
level. More implementations and claims never lower its own evidence, and
stronger own evidence, or stronger evidence for its calls, never
lowers what is reported:

```fren
expect more_evidence_never_lower: forall (a b: direct) (ra rb: rank),
    when (not a.proved? or b.proved?) and (not a.solver? or b.solver?)
    and (not a.tested? or b.tested?) and (not a.trusted? or b.trusted?)
    and ra.level = a.level and rb.level = b.level,
    ra.r <= rb.r

expect stronger_parts_never_lower: forall (a b: evidence) (oa ob wa wb ra rb: rank),
    when a.has_outputs? = b.has_outputs?
    and oa.level = a.own and ob.level = b.own and oa.r <= ob.r
    and wa.level = a.weakest and wb.level = b.weakest and wa.r <= wb.r
    and ra.level = a.level and rb.level = b.level,
    ra.r <= rb.r
```

## The report

The report counts the procedures at each level and lists those below
`proved`, by level. For the procedures of a spec, it is the same from
`fren trace` and `#fren_trace`, except that the `fren` command does not
check implementations, so under it no procedure is above `tested`.
`#fren_trace` reports at the end of the Lean file that contains it, so it
covers the procedures declared before it, including those of imported
modules.

Given a minimum level, with `--require` or `fren.requireEvidence`, each
procedure below it is a warning, at the procedure's declaration.
`trace::required` gives the severity for one procedure.

```fren
pub proc required(
    level: Level,
    threshold: Level,    -- the level named by `fren.requireEvidence`
    enforced?,           -- the option is set
): (severity: Severity) {
    call l := rank(level)
    call t := rank(threshold)

    ensure below: severity = if enforced? and l.r < t.r then Warning else Silent

    expect opt_in: unless enforced?, severity = Silent
    expect proved_always_enough: when level = Proved, severity = Silent
}

expect stronger_never_warns: forall (a b: required) (ra rb: rank),
    when a.threshold = b.threshold and a.enforced? = b.enforced?
    and ra.level = a.level and rb.level = b.level and ra.r <= rb.r and b.severity = Warning,
    a.severity = Warning
```

## Claims

The checks of claims and markers are those described in
[Claims](#claims) and [Scanning tests](#scanning-tests).
`trace::tested_file` gives whether a file named by a `tested` claim is
accepted.

```fren
pub proc tested_file(
    exists?,
    covers?,             -- it has a `fren-covers:` marker naming the procedure
): (accepted?) {
    ensure rule: accepted? iff (exists? and covers?)
}
```

`trace::covers_line` gives whether a procedure named by a `fren-covers:`
marker in a scanned file is accepted.

```fren
pub proc covers_line(
    component_exists?,
    claimed?,            -- a `tested` claim for the procedure names this file
): (accepted?) {
    ensure rule: accepted? iff (component_exists? and claimed?)
}
```

`trace::trusted_claim` gives whether a `trusted` claim is accepted, for
any justification, the text of its string literal with surrounding
whitespace removed:

```fren
pub proc trusted_claim(
    why: String,         -- the justification, trimmed
): (accepted?) {
    ensure rule: accepted? iff why != ""

    expect empty_rejected: when why = "", not accepted?
}
```

`trace::trace_exit` gives the exit status of `fren trace`. A static error,
including a claim that fails its checks, means that there is no report, and
the status is 2. Otherwise a procedure below `--require`, or a marker that
no claim names, makes the status 1.

```fren
pub proc trace_exit(
    ran?,                -- no static errors
    below?,              -- some procedure is below `--require`
    stray?,              -- some marker in a scanned file names no claim for it
): (code: Int) {
    ensure not_run: unless ran?, code = 2
    ensure failed: when ran? and (below? or stray?), code = 1
    ensure passed: when ran? and not below? and not stray?, code = 0

    expect zero_means_clean: when code = 0, ran? and not below? and not stray?
}

use cli::exit_status

refine trace_exit_status: trace_exit refines exit_status

#fren_check
```
