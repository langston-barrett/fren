# Mutation testing

```
fren mutate [--by solver|testing|both] [--comp PATH] [--mutant ID]... [--sample N] [--seed N] [--list]
    [--timeout SECONDS] [--tests N] [-A|-W|-D|-F LINT]... FILE...
```

`fren mutate` makes small changes to a spec's constraints and definitions,
checks each changed spec, a *mutant*, and reports the mutants that no
check rejects. A surviving mutant points at something that the
expectations, refinements and instance assumptions do not pin down: either
the spec says less than intended, or an expectation is missing. This is a
cousin of the [vacuity](Check.md#vacuity) and
[redundancy](Check.md#redundancy) checks, for whole specs. With
`--by both`, mutants that the solver's checks reject but that
[testing](Eval.md#fren-quickcheck) does not show where testing's search is
weak.

```fren
pub mod mutate

use check::Verdict
use check::Verdict::{Fail, Pass}
use cli
use view::Severity
use view::Severity::{Error, Silent, Warning}
```

## Mutants

Each mutant changes one place in one file. The changes are made to the
parsed spec, so every mutant parses: a change that would make an operator
bind differently adds parentheses, and an operand that replaces its
operator keeps its own. The changes are:

| Origin | Change |
|---|---|
| `swap-comparison` | `<` and `<=`, `>` and `>=`, `=` and `!=`, each to the other, including each operator of a [chained comparison](Lang/Expressions.md#chained-comparisons) |
| `swap-and-or` | `and` and `or`, each to the other |
| `swap-arithmetic` | `+` and `-`, and `div` and `mod`, each to the other |
| `drop-conjunct` | `a and b` to `a`, and to `b`; a chained comparison to itself without its first comparison, and without its last |
| `negate-trigger` | `when` and `unless`, each to the other |
| `shift-integer` | an integer literal `n` to `n + 1`, and to `n - 1` if `n > 0`, written in decimal |
| `flip-bool` | `true` and `false`, each to the other |
| `remove-element` | an element of a set or sequence literal of at least two, removed |
| `swap-repetition` | in a [regular-expression pattern](Lang/Expressions.md#patterns), `*` and `+`, each to the other |
| `narrow-class` | in a regular-expression pattern, an item of a class of at least two, removed, unless that leaves a `^` first, which would negate the class |
| `drop-alternative` | an alternative of the pattern of a [pattern test](Lang/Expressions.md#pattern-tests) of at least two, removed, with its `\|` |

A regular-expression pattern is changed only where its text is its
value: a raw literal, or a literal without escapes.

A [divisor](Lang/Expressions.md#division-and-remainder) is never made `0`,
which would be a static error: `shift-integer` does not change a divisor
`1` to `0`, and a constant that a divisor names is not changed at all, nor
is a constant that the value of such a constant names. A constant is told
by its name alone, in any of the files.

Mutants change what a spec asserts: the expressions of `assume`s, `req`s,
defined outputs, instance bindings, constants and defined functions. The
expectations, both of components and [global](Lang/Global.md), are what
rejects mutants, and their text is not changed. But an expectation that
reads a constant or function reads the mutant's: if a requirement and an
expectation both say `x <= LIMIT`, changing `LIMIT` moves both, and no
check rejects it. Such a survivor says that nothing pins the constant down
independently, such as an expectation with its value written out; its
warning says so. Mutating an assumption checks the
[instance assumption](Check.md#instance-assumptions) checks and
refinements that rely on it.

## Identifiers

Each mutant has an identifier, `ORIGIN-ITEM-HASH`, such as
`swap-comparison-cli::exit::failed-0a1b2c3d4e5f`. `ITEM` is the path of
the item changed: a constraint, defined output or instance as
`module::component::name`, or a constant or function as `module::name`,
where `name` is the name declared, without the `!` of a
[shadowing](Lang/Components.md#shadowing) declaration (so `y!` is named
`y`), with each run of characters other than ASCII letters, digits, `_` and `:`
made one `_`, and `_` trimmed next to `::` and at both ends. `HASH` is 12
hexadecimal digits of the 64-bit FNV-1a hash, the same on every machine
and build, of the origin, the file's path without `.` segments or
repeated `/`, the item, the expression changed and the change, with
whitespace and the commas that end a list removed, and how many identical
mutants come before it in the item. So an identifier stays the same when
the spec is reformatted, or changed elsewhere, and `--mutant ID`
names the same mutant across runs.

## Killing mutants

A mutant is checked as `fren check` checks the spec, including the checks
set to [testing](Check.md#checking-by-testing) and the
[refinements](Lang/Refinement.md), or with `--by testing`, as `fren
quickcheck` tests it. Only the components, global expectations and
refinements whose formulas the mutant changes are checked, and the spec's
own: the others' results cannot change. A check *kills* a mutant if it
passes on the spec and fails on the mutant. A check that does not pass on
the spec itself, failing or inconclusive, kills nothing. The number of
such checks among those run is reported once, as a note, counting a check
once even if both the solver and testing ran it. `mutate::kill` states
this:

```fren
pub comp kill {
    in before: Verdict    -- the check's verdict on the spec
    in after: Verdict     -- its verdict on the mutant
    pub det out kills?

    req rule: kills? iff (before = Pass and after = Fail)

    expect failing_kills_nothing: when before = Fail, not kills?
    expect only_failures_kill: when after != Fail, not kills?
}
```

A mutant on which a check that passes on the spec is only inconclusive is
not killed: if nothing else kills it, it survives, and its warning says
that some check was inconclusive. The checks of the spec and of a mutant are matched by their kind, and the
constraint, instance or variable that they are about. The
[definedness](Check.md#definedness) checks of one constraint are one
check, which passes when every index in it is in range: an index has no
name but its position, which a mutant that adds or drops one changes. A
redundancy counts as a failure: a mutant that makes a constraint
redundant is killed by that check.

A mutant that has a static error, from a lint set to `deny` or `forbid`, is
*unviable*: it is not checked, and is left out of the kill rate. Any other
static error in a mutant is an internal error, since mutants are made so
as to have none; such a mutant is counted as unviable too. An evaluator
that cannot read a mutant is an internal error as well.

### Equivalent mutants

Some mutants mean what the spec means, such as `x > 0` changed to
`x >= 1`, and no check can kill them. For a mutant that survives, the
solver is asked whether each formula that the mutant changes, in each
component and global expectation, and each defined function that it
changes, equals the spec's for all values of the variables and every
[interpretation](Lang/Components.md#interpretations). If so, the mutant
is *equivalent*, and is not reported. If the solver cannot tell within a
second, which can happen outside the [decidable
core](Lang/Decidability.md), the mutant is reported, with a note that it
may be equivalent. `mutate::outcome` gives what becomes of a mutant:

```fren
pub enum Outcome { Killed, Survived, Equivalent, Unviable }

use self::Outcome::{Equivalent, Killed, Survived, Unviable}

pub comp outcome {
    in viable?          -- the mutant has no static errors
    in killed?          -- some check kills it
    in equivalent?      -- the solver shows that it means what the spec means
    pub det out outcome: Outcome

    req unviable: unless viable?, outcome = Unviable
    req killed: when viable? and killed?, outcome = Killed
    req equivalent: when viable? and not killed? and equivalent?, outcome = Equivalent
    req survived: when viable? and not killed? and not equivalent?, outcome = Survived

    expect reported_unexplained: when outcome = Survived, viable? and not killed? and not equivalent?
    expect kills_win: when viable? and killed?, outcome != Equivalent
}
```

### Choosing the checker

`--by solver`, the default, checks mutants with the solver, as `fren
check` does, with `--timeout` for each query. A query of a mutant that is
also a query of the spec, or of an earlier mutant, word for word, such as
the consistency of assumptions that the mutant leaves alone, gets the
answer that it got first, without the solver
([Solver queries](Cli.md#solver-queries)). `--by testing` tests them,
as `fren quickcheck` does, with `--tests` tests per component (default
100) from `--seed`. `--by both` does both, and a mutant is killed if
either kills it. A mutant that the solver's checks kill but testing does
not is *missed by testing* (`F0614`): testing's search does not find the
behaviours that tell it apart from the spec. The solver's side includes the
checks set to testing, as `fren check` runs them, so a component whose
checks are all set to testing has no mutant missed by testing. `mutate::missed` states
this:

```fren
pub comp missed {
    in by_solver?       -- the solver's checks kill the mutant
    in by_testing?      -- testing kills it
    pub det out missed?

    req rule: missed? iff (by_solver? and not by_testing?)

    expect killed_by_testing: when by_testing?, not missed?
    expect killed_by_the_solver: when missed?, by_solver?
}
```

## Selecting mutants

`--comp PATH` selects the mutants of the component `PATH`; `--mutant ID`
selects the mutant `ID`, and may be repeated. Given both, a mutant must
meet both. A `--comp` or `--mutant` that the spec does not have is an
error in the arguments, and `fren mutate` exits with 2. `--sample N` then
takes `N` of the selected mutants, chosen by
`--seed` (default 0). The same seed starts testing's search, so with
`--by testing` or `--by both`, a different seed also tests differently. Whether a mutant
is taken depends only on its identifier and the seed, so a larger sample
contains a smaller one. `--list` writes the selected mutants to standard
output, one per line, with their identifier, position and change, and
checks nothing:

```text
swap-comparison-c::r-0a1b2c3d4e5f spec.fren:4:21 `>` changed to `>=`
```

## Output

Each surviving mutant is a warning, `F0613`, at the change, with the
mutant shown as a suggested edit. After them comes a summary, on
standard error:

```text
fren: 12 mutants: 9 killed, 2 survived, 1 equivalent, 0 unviable
```

With `--by both`, it ends with the number missed by testing, as
`, 1 missed by testing`.

Standard output holds the kill rate of each component, and of each
constant and function, sorted by path: the share of its mutants that were
killed, out of those killed or surviving, rounded down to a whole
percentage.

```text
m::c: 9 of 11 mutants killed (81%), 1 equivalent
```

The line ends with the numbers of equivalent and unviable mutants, and with
`--by both` of those missed by testing, each where it is not 0.

Lints are reported on the spec as `fren check` reports them, but only
surviving and missed mutants and internal errors decide the exit status:
a lint that warns does not. `mutate::exit` gives the exit status. It is `fren check`'s
(`cli::exit`), where each surviving or missed mutant is a warning and each
internal error an error, and so it follows the convention of every command
(`cli::exit_status`):

```fren
pub comp exit {
    in ran?             -- the spec and the arguments have no errors
    in survived?        -- some mutant survived, or was missed by testing
    in internal?        -- some internal error was reported
    pub det out code: Int

    out worst: Severity := if internal? then Error else if survived? then Warning else Silent
    inst ends: cli::exit { ran?, worst }
    req as_check: code = ends.code

    expect not_run: unless ran?, code = 2
    expect internal_fails: when ran? and internal?, code = 1
    expect survivors_warn: when ran? and not internal? and survived?, code = 3
    expect zero_means_all_killed: when code = 0, ran? and not survived? and not internal?
}

use cli::exit_status

refine mutate_exit_status: exit refines exit_status

#fren_check
```

`fren mutate --list` exits with 0, or with 2 if it could not run.
