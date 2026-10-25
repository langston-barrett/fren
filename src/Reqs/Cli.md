# The `fren` command

```
fren check [--timeout SECONDS] [--dump-smt] [--tests N] [--seed N] [-A|-W|-D|-F LINT]... FILE...
fren trace [--tests GLOB]... [--require LEVEL] [-A|-W|-D|-F LINT]... FILE...
fren fmt [--check] [--ignore GLOB]... FILE...
fren fix [--check] [--fmt] [--only LINT]... [--skip LINT]... [--ignore GLOB]... [-A|-W|-D|-F LINT]... FILE...
fren eval --comp PATH [--set VAR=VALUE]... [--seed N] [-A|-W|-D|-F LINT]... FILE...
fren quickcheck [--tests N] [--seed N] [-A|-W|-D|-F LINT]... FILE...
fren mutate [--by solver|testing|both] [--comp PATH] [--mutant ID]... [--sample N] [--seed N] [--list]
    [--timeout SECONDS] [--tests N] [-A|-W|-D|-F LINT]... FILE...
fren --explain CODE
fren --help
fren --version
```

Every form also takes `--color WHEN` (or `--color=WHEN`), anywhere among
its arguments; see [Colour](#colour).

`fren check` checks the spec in the given files, without Lean. `fren trace`
reports the [evidence](Trace.md) for every component of the spec, and scans
the tests for `fren-covers:` markers that no claim names; it does not run
the checks. `fren fmt` [formats](Fmt.md) the files, and `fren fix`
[fixes](Lint.md#fixing-lints) the lints that it can. `fren eval`
evaluates a component on one behaviour, and `fren quickcheck` tests the
spec on random behaviours, both without the solver (see [Evaluation and
testing](Eval.md)). `fren mutate` checks small changes to the spec, and
reports those that no check rejects (see [Mutation
testing](Mutate.md)). `fren --explain CODE` explains an [error
code](View.md#error-codes), such as `F0105`. `fren --help`
(or `-h`) prints a usage summary, and `fren --version` (or `-V`) prints the
version. `fren` is a self-contained executable: it needs no Lean
installation. It is built by `lake build fren`.

| Option | Meaning |
|---|---|
| `--timeout SECONDS` | `check` and `mutate`: time limit for each solver query (default 10) |
| `--dump-smt` | `check`: write each solver query to standard output; see [Solver queries](#solver-queries) |
| `--tests GLOB` | `trace`: scan the matching files for markers; may be repeated |
| `--require LEVEL` | `trace`: warn about, and fail on, components with weaker evidence than `trusted`, `tested`, `solver` or `proved` |
| `--check` | `fmt` and `fix`: change no file, and print a diff of what would change |
| `--ignore GLOB` | `fmt`: skip the matching files; `fix`: leave them as they are; may be repeated |
| `--fmt` | `fix`: then format the files, as `fren fmt` does |
| `--only LINT`, `--skip LINT` | `fix`: fix only the lints given, or all but them; may be repeated |
| `-A LINT`, `-W LINT`, `-D LINT`, `-F LINT` | `check`, `trace`, `fix`, `eval`, `quickcheck` and `mutate`: set the level of a [lint](Lint.md), or of each lint of a [group](Lint.md#groups), to `allow`, `warn`, `deny` or `forbid`; may be repeated. The long forms are `--allow`, `--warn`, `--deny` and `--forbid` |
| `--comp PATH` | `eval`: the component to evaluate; `mutate`: the component whose mutants to check |
| `--set VAR=VALUE` | `eval`: the value of a variable; may be repeated |
| `--seed N` | `eval`, `quickcheck`, `mutate`, and `check` for [checks by testing](Check.md#checking-by-testing): where the random search starts (default 0); `mutate`: also which mutants `--sample` takes |
| `--tests N` | `quickcheck` and `mutate`: tests per component and global expectation; `check`: tests per component or global expectation with [checks by testing](Check.md#checking-by-testing) (default 100) |
| `--by WHAT` | `mutate`: check mutants with the `solver` (the default), by `testing`, or `both` |
| `--mutant ID` | `mutate`: check the mutant `ID`; may be repeated |
| `--sample N` | `mutate`: check `N` of the mutants |
| `--list` | `mutate`: list the mutants, and check none |
| `--color WHEN` | colour the output: `auto` (the default), `always` or `never` |

## Input files

- A file whose name ends in `.md` is a [Markdown spec](Markdown.md). Any
  other file is read as Fren source, conventionally with the extension
  `.fren`.
- A file may start with `import` and `open` lines, which are skipped, so a
  Lean file that contains only a spec can be checked too. `#fren_check` is
  accepted and ignored. `set_option` is accepted only to set the level of a
  [lint](Lint.md#setting-levels). Any other Lean code, including [Lean-only
  items](Lang/Items.md#lean-only-items) and other options, is an error.
- The files are processed in the order given, with one shared set of modules
  (see [Modules and visibility](Lang/Modules.md#across-files)). Then every
  component and [global expectation](Lang/Global.md) is checked, or for
  `fren trace`, the evidence for every component is reported. Unlike in
  Lean, this includes those that no `#fren_check` follows.

## Output

Diagnostics, and the summary of the checks, go to standard error. Standard
output holds only what was asked for: the evidence report of `fren trace`,
the evaluated behaviour of `fren eval`, the kill rates and the list of
mutants of `fren mutate`, the diffs of `fren fmt --check` and `fren fix --check`, the [solver queries](#solver-queries) of `fren check --dump-smt`, and the
text of `--explain`, `--help` and `--version`.

Each [diagnostic](View.md) is printed with a header
with the severity and [error code](View.md#error-codes), the position as
`file:line:col` (both counted from 1), the source line with the offending
part underlined, notes and help, and suggested edits:

```text
error[F0105]: `==` is not an operator in Fren
 --> spec.fren:2:47
  |
2 | comp c { in x: Int pub out y? req r: y? iff x == 1 }
  |                                               ^^ not a Fren operator
  |
help: use `=` to test for equality
  |
2 - comp c { in x: Int pub out y? req r: y? iff x == 1 }
2 + comp c { in x: Int pub out y? req r: y? iff x = 1 }
  |
```

Information, such as the requirements that conflict in an unrealizable
component, is printed as a `note`. After the diagnostics come the summary
of the checks, or, if there were static errors, their count, and then a
pointer to `fren --explain` for the codes reported.

```fren
pub mod cli

use check::{Kind, Verdict}
use view::Severity
use view::Severity::{Error, Info, Silent, Warning}
```

## Solver queries

With `--dump-smt`, `fren check` writes each query it gives the solver to
standard output, as an [SMT-LIB](https://smt-lib.org/) script, before the
query runs. Each script starts with a comment naming its component and
numbering the query within it, names each hypothesis in a comment after
its `assert`, and ends with `(check-sat)` and `(reset)`, so the whole
stream can be given to a solver such as cvc5:

```text
fren check --dump-smt spec.fren > queries.smt2
cvc5 queries.smt2
```

The scripts declare variables as quoted symbols, such as `|y|`, and
abstract types as sorts and functions as uninterpreted functions, named by
their paths after `::`, such as `|::lang::Name|`, which no variable can be
named. A second
copy of a variable, as used by the [determinism](Check.md#determinism)
check, is primed: `|y'|`. A script declares every variable of its
component, but of the spec's abstract types, enumerations, records and
functions only those that its query mentions, directly or through
another declaration: the others cannot change its answer, and declaring
them all is most of the work of a small query.

Each script sets the [SMT-LIB logic](https://smt-lib.org/logics.shtml) of
its query, so that the solver rejects a query outside the fragment that
Fren's rules keep it in, rather than running an incomplete procedure:
linear integer arithmetic, uninterpreted functions and datatypes (for
enumerations and records). A `match` arm reads the payload with the
datatype's selectors, and tests its scrutinee by comparing it with the
variant built from them. A string literal is written as SMT-LIB writes
it: `""` for `"`, and `\u{h}` for `\` and for every character outside
printable ASCII. Only the [realizability](Check.md#realizability) check
quantifies, over outputs, which never occur in a function's arguments (see
[Instances](Lang/Instances.md#instance-variables)). A spec that uses
strings needs the theory of strings, which has no smaller standard logic,
so its queries use `ALL`, and set cvc5's options `strings-exp`, without
which cvc5 refuses some string operations, `re-inter-mode all`, so
that it decides intersections of [patterns](Lang/Expressions.md#patterns),
and `re-elim on`, so that it rewrites a match that needs no automaton,
such as one of `x[0-9]{2}.*`, as string functions, which it decides
faster. These rewrites keep the query's meaning, and introduce no
quantifiers.
A spec that uses sets uses `ALL` too, and sets `sets-exp`, without which
cvc5 refuses to count the members of a set of a finite type. A relation's
`domain` is its join with the set of every value of the second type, and
its `range` the same on the other side, written as a literal when that type
is finite. Over a type that is not finite, which is outside the core, they
are cvc5's projections, which it supports only in higher-order logic, so
such a spec uses `HO_ALL`. The Lean-hosted front end does the same, for
each query with a projection, by cvc5's option `force-logic`, since
lean-smt always sets `ALL`. Its queries are still in the
[decidable core](Lang/Decidability.md), unless it opts out. `cli::logic`
gives the logic from the check, where `QuantifierFree` is `QF_UFDTLIA`,
`Quantified` is `UFDTLIA` and `HigherOrder` is `HO_ALL`:

```fren
pub enum Logic { QuantifierFree, Quantified, All, HigherOrder }

pub enum Theory { Strings, Sets, Sequences }

pub comp logic {
    use check::Kind::Realizability
    use self::Logic::{All, HigherOrder, Quantified, QuantifierFree}
    use self::Theory::{Sequences, Sets, Strings}
    in kind: Kind
    in theories: Set(Theory)     -- beyond uninterpreted functions, datatypes and linear integer arithmetic
    in projection?               -- the spec takes the domain or range of a relation over a type that is not finite
    pub det out logic: Logic
    pub det out strings_exp?     -- set cvc5's `strings-exp`, `re-inter-mode` and `re-elim` options
    pub det out sets_exp?        -- set cvc5's `sets-exp` option

    req base: when theories = {},
        logic = (if kind = Realizability then Quantified else QuantifierFree)
    assume relations_are_sets: when projection?, Sets in theories

    req all: when theories != {}, logic = (if projection? then HigherOrder else All)
    -- cvc5 decides sequences in its strings solver.
    req options: (strings_exp? iff (Strings in theories or Sequences in theories))
        and (sets_exp? iff (Sets in theories or Sequences in theories))

    expect quantifier_free_when_possible: when logic = QuantifierFree, kind != Realizability
    expect sets_alone: when theories = {Sets}, not strings_exp?
    expect higher_order_rarely: when logic = HigherOrder, projection?
}
```

In Lean, the queries are the same, but lean-smt sets the logic `ALL`.

## Exit status

| Status | Meaning |
|---|---|
| 0 | every check passed |
| 1 | some result is an error: a check failed |
| 2 | the checks could not run: an unreadable file, bad arguments, or a static error, including a denied lint |
| 3 | no result is an error, but some diagnostic is a warning: a check was inconclusive, a constraint is redundant, or a [lint](Lint.md) warned |

`fren quickcheck` exits as `fren check` does, and so does `fren mutate`,
with each surviving mutant a warning (`mutate::exit`). Every command follows one
convention, which `cli::exit_status` states: 2 exactly when the command
could not run, and otherwise 0, 1 or 3, with 0 meaning that there is
nothing to report. What 1 and 3 mean is each command's own:

- `fren check` and `fren quickcheck`, the table above (`cli::exit`);
- `fren eval`, a behaviour that does not meet the component, and one
  that could not be completed (see [Evaluation and
  testing](Eval.md#fren-eval), `eval::eval_exit`);
- `fren trace`, a component below `--require` or an unclaimed marker
  (`trace::trace_exit`);
- `fren fmt` and `fren fix`, with `--check`, a file that would change (see
  [Formatting](Fmt.md#exit-status) and [Fixing
  lints](Lint.md#fixing-lints)).

`cli::exit`, `eval::eval_exit`, `trace::trace_exit` and `mutate::exit`
refine `exit_status`. So do `fmt::exit` and `lint::fix_exit`, which say
whether the command could run in terms of what it read, `all_parsed?` and
`loaded?`: their refinements bind `ran?` to it (see
[Bindings](Lang/Refinement.md#bindings)).

```fren
pub comp exit_status {
    in ran?                -- the command could run
    pub out code: Int

    req not_run: code = 2 iff not ran?
    req documented: code = 0 or code = 1 or code = 2 or code = 3
}
```

`cli::exit` gives the exit status, from whether the checks ran and the
most severe [level](View.md#severity) of their results and of the
[lints](Lint.md) reported along the way:

```fren
pub comp exit {
    in ran?                -- no static errors: checks ran
    in worst: Severity     -- the most severe level over all results and lints
    pub det out code: Int

    req not_run: unless ran?, code = 2
    req failed: when ran? and worst = Error, code = 1
    req warned: when ran? and worst = Warning, code = 3
    req passed: when ran? and (worst = Silent or worst = Info), code = 0

    expect zero_means_no_problem: when code = 0, ran? and worst != Error and worst != Warning
    expect documented_codes: code >= 0 and code <= 3
}

refine check_exit_status: exit refines exit_status
```

`cli::worst_severity` gives the most severe level over all results and
lints of a run, from the levels present among them:

```fren
pub comp worst_severity {
    in present: Set(Severity)    -- the levels of the run's results and lints
    pub det out worst: Severity

    req any_error: when Error in present, worst = Error
    req warning: when not Error in present and Warning in present, worst = Warning
    -- Includes runs with no checks at all.
    req silent: unless Error in present or Warning in present, worst = Silent

    expect worst_present: when worst != Silent, worst in present
}
```

`cli::run` combines the two: the levels present decide the exit status.

```fren
pub comp run {
    in ran?
    in present: Set(Severity)
    pub det out code: Int

    inst counted: worst_severity { present }
    inst ends: exit { ran?, worst := counted.worst }

    req exit_code: code = ends.code

    expect error_exits_1: when ran? and Error in present, code = 1
    expect warning_exits_3: when ran? and not Error in present and Warning in present, code = 3
    expect clean_exits_0: when ran? and not Error in present and not Warning in present, code = 0
}
```

Put together with the [severity of a result](View.md#severity), this says
what a check's verdict does to the exit status, across the chapters: a
check that fails, other than as redundant, makes `fren check` exit with 1,
whatever else is reported. A check that passes is silent, so a run whose
checks all pass reports at most information and exits with 0, and one in
which a check is inconclusive and nothing worse is reported exits with 3:

```fren
use view::severity

expect failing_check_exits_1: forall (s: severity) (r: run),
    when r.ran? and s.level in r.present and s.verdict = Verdict::Fail and s.kind != Kind::Redundancy,
    r.code = 1

expect passing_checks_exit_0: forall (s: severity) (r: run),
    when r.ran? and s.verdict = Verdict::Pass and r.present subset {s.level, Info},
    s.level = Silent and r.code = 0

expect inconclusive_exits_3: forall (s: severity) (r: run),
    when r.ran? and s.verdict = Verdict::Inconclusive and s.level in r.present
    and r.present subset {s.level, Info},
    r.code = 3
```

## Colour

The `fren` command colours its diagnostics: the severity's
colour for the header and the underline, blue for the gutter, and red and
green for what a suggested edit removes and adds. `cli::color` says when
they are coloured, from `--color` and whether standard error, where they
go, is a terminal. With `auto`, the environment can turn
colour off, following the [`NO_COLOR`](https://no-color.org/) convention
and the `dumb` terminal of `TERM`; `always` and `never` override it.

```fren
pub enum ColorChoice { Auto, Always, Never }

use self::ColorChoice::{Always, Auto, Never}

pub comp color {
    in choice: ColorChoice
    in tty?        -- standard error is a terminal
    in no_color?   -- `NO_COLOR` is set and not empty
    in dumb?       -- `TERM` is `dumb`
    pub out colored?

    req always: when choice = Always, colored?
    req never: when choice = Never, not colored?
    req auto: when choice = Auto, colored? iff (tty? and not no_color? and not dumb?)

    -- Piped output, as in tests and logs, is plain unless asked for.
    expect pipes_plain: when not tty? and choice != Always, not colored?
    expect forced: when choice = Always, colored?
}
```

## Agreement with Lean

For the same results, the exit status is 1 exactly when a Lean build fails,
and nonzero exactly when `lake build --wfail` fails (see
[Diagnostics](View.md#severity)). `cli::agrees_with_build` confirms this:

```fren
use view::build

pub comp agrees_with_build {
    in worst: Severity

    inst hosted: build { worst }
    inst standalone: exit { ran? := true, worst }

    expect failing: standalone.code = 1 iff hosted.fails?
    expect wfail: standalone.code != 0 iff hosted.fails_wfail?
}
```

The `fren` command shares Fren's grammar, name resolution and checks with
Lean. It accepts only Fren, including the `tested` and `trusted` claims of
[Traceability](Trace.md): anything that needs Lean, such as `impl`, is a
static error rather than being ignored. `cli::accepts` states this:

```fren
pub enum Construct { Fren, LeanCode }

use self::Construct::Fren

pub comp accepts {
    in construct: Construct
    pub out accepted?

    req fren_only: accepted? iff construct = Fren
}
```

On a spec that both accept, Lean and the `fren` command give every check
the same verdict, except a [check by testing](Check.md#checking-by-testing),
which only the `fren` command runs, and for failures name the same conflicting or ruling-out
constraints. Counterexample values may differ. `cli::agreement` states
this:

```fren
pub enum FrontEnd { Hosted, Standalone }

pub comp agreement {
    in hosted: Verdict
    pub out standalone: Verdict

    req same_verdict: standalone = hosted
}

#fren_check
```
