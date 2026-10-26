# Mutation testing

```
fren mutate [--by solver|testing|both] [--comp PATH] [--mutant ID]... [--sample N] [--seed N] [--list]
    [--timeout SECONDS] [--resource-limit N] [--tests N] [-A|-W|-D|-F LINT]... FILE...
```

`fren mutate` makes small changes to a spec's constraints and definitions,
checks each changed spec, a *mutant*, and reports the mutants that no
check rejects. A surviving mutant points at something that the
expectations, cover goals, refinements and instance assumptions do not
pin down: either the spec says less than intended, or an expectation or a
cover goal is missing. This is a
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
| `swap-arithmetic` | `+` and `-`, and `div` and `mod`, each to the other, except a `+` where a [`Nat`](Lang/Types.md#natural-numbers) is expected, since `-` gives an `Int` |
| `drop-conjunct` | `a and b` to `a`, and to `b`; a chained comparison to itself without its first comparison, and without its last |
| `negate-trigger` | `when` and `unless`, each to the other |
| `swap-quantifier` | `forall` and `exists`, each to the other, in a [quantifier](Lang/Quantifiers.md) of an expression |
| `shift-integer` | an integer literal `n` to `n + 1`, and to `n - 1` if `n > 0`, written in decimal |
| `flip-bool` | `true` and `false`, each to the other |
| `remove-element` | an element of a set or sequence literal of at least two, removed |
| `swap-repetition` | in a [regular-expression pattern](Lang/Expressions.md#patterns), `*` and `+`, each to the other |
| `narrow-class` | in a regular-expression pattern, an item of a class of at least two, removed, unless that leaves a `^` first, which would negate the class |
| `drop-alternative` | an alternative of the pattern of a [pattern test](Lang/Expressions.md#pattern-tests) of at least two, removed, with its `\|` |
| `swap-cardinality` | `exactly_one?` and `at_most_one?`, the [cardinality operators](Lang/Expressions.md#cardinality), each to the other |
| `drop-argument` | an argument of a cardinality operator of at least two, removed, with its `,` |
| `swap-rows` | the values of two consecutive rows of a [table](Lang/Expressions.md#tables), each to the other's, unless they are written the same |
| `drop-row` | a row of a table of at least two, removed, with its `\|` |
| `shift-variant` | a variant without a payload, in an expression, to the variants without a payload just before and just after it in its [enumeration](Lang/Items.md#enumerations), written as it is written: as `E::W` after `E::V`, and as `W` after `V` only if `use`s bring both into scope by their own names from the same enumeration, and no binder shadows `V` |
| `swap-branches` | `if c then a else b` to `if c then b else a`, unless `a` and `b` are written the same |
| `drop-negation` | `not e` to `e`, and `-e` to `e` |
| `drop-trigger` | `when c, e` and `unless c, e` to `e` |
| `drop-update` | a field of a [record update](Lang/Expressions.md#record-updates) of at least two fields, removed, with its `,` |
| `swap-arms` | the values of two consecutive arms of a `match`, each to the other's, unless either arm's pattern binds a name, or they are written the same |
| `swap-min-max` | `x.min(y)` and `x.max(y)`, each to the other |
| `swap-affix` | `s.starts_with?(p)` and `s.ends_with?(p)`, each to the other |

An enumeration is told by its name alone, as a constant is: two
enumerations of one name, in different modules, have no `shift-variant`
mutants. Its neighbours are those of an ordered enumeration's order, so
that `shift-variant` moves a variant across a comparison's boundary as
`shift-integer` moves an integer. The values of `match` arms whose patterns
bind names are left in place, since a value may read a name that the other
arm's pattern does not bind.

A regular-expression pattern is changed only where its text is its
value: a raw literal, or a literal without escapes. A table's values all
have its type, so swapping two keeps it well typed, and dropping a row
never leaves one after `_`. Dropping a row that some case needs makes the
table incomplete, which the [completeness check](Check.md#completeness)
reports, so it kills the mutant even when no expectation does.

A [divisor](Lang/Expressions.md#division-and-remainder) is never made `0`,
which would be a static error: `shift-integer` does not change a divisor
`1` to `0`, and a constant that a divisor names is not changed at all, nor
is a constant that the value of such a constant names. A constant is told
by its name alone, in any of the files.

The [patterns](Lang/Patterns.md) of `match` arms are not changed, so that
every mutant's `match` stays exhaustive and every arm reachable, and only
the top-level alternatives of a pattern test's pattern are dropped:
dropping an alternative never makes another unreachable. For the same
reason, a constant that bounds a range pattern is left alone as a divisor's
is, since its value decides whether a range is empty and which arms the
ranges reach.

Mutants change what a spec asserts: the expressions of `assume`s, `ensure`s,
defined outputs, instance bindings, constants and defined functions,
including the definitions of their [`let`s and `where`
clauses](Lang/Let.md), which are changed like any other expression. The
expectations, both of components and [global](Lang/Global.md), and the
[cover goals](Lang/Components.md#cover-goals) are what rejects mutants,
and their text is not changed; nor is that of a function's
[contract](Lang/Items.md#contracts), which a defined function's body is
checked against. An expectation rejects a mutant that
weakens what the spec says, and a cover goal one that strengthens it: a
mutant that rules out a goal's scenario fails the goal, which kills it. But an expectation that
reads a constant or function reads the mutant's: if a guarantee and an
expectation both say `x <= LIMIT`, changing `LIMIT` moves both, and no
check rejects it. Such a survivor says that nothing pins the constant down
independently, such as an expectation with its value written out; its
warning says so. Mutating an assumption checks the
[instance assumption](Check.md#instance-assumptions) checks and
refinements that rely on it.

## Identifiers

Each mutant has an identifier, `ORIGIN-ITEM-HASH`, such as
`swap-comparison-cli::exit::code_rule-0a1b2c3d4e5f`. `ITEM` is the path of
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
once even if both the solver and testing ran it, and the definedness
checks of a constraint as one (see below), so it can be smaller than the
number of failures that `fren check` reports. `mutate::kill` states
this:

```fren
pub comp kill {
    in before: Verdict    -- the check's verdict on the spec
    in after: Verdict     -- its verdict on the mutant
    pub det out kills?

    ensure rule: kills? iff (before = Pass and after = Fail)

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
name but its position, which a mutant that adds or drops one changes.
Likewise, its [completeness](Check.md#completeness) checks are one check,
and so are its [disjointness](Check.md#disjointness) checks, since a
mutant that drops a row renumbers the rows. A
redundancy counts as a failure: a mutant that makes a constraint
redundant is killed by that check.

A component, global expectation or refinement is checked again only if
the mutant changes what its checks read: its formulas, its variables, and
the spec's declarations (its *fingerprint*). Skipping the others loses no
kill, since a check's verdict depends only on what it reads, up to the
solver's time limit. `mutate::skip` states this:

```fren
pub comp skip {
    in changed?         -- the mutant changes the fingerprint of the check's item
    in before: Verdict  -- the check's verdict on the spec
    in after: Verdict   -- its verdict on the mutant
    pub det out run?    -- the check runs on the mutant

    assume determined: unless changed?, after = before

    ensure rule: run? iff changed?

    inst k: kill { before, after }
    expect skipped_kill_nothing: unless run?, not k.kills?
}
```

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
[interpretation](Lang/Components.md#interpretations). The formula of an
item's indexes says that each is in range, and is `true` for an item
with none, such as after a mutant drops its last index. If each is equal,
the mutant is *equivalent*, and is not reported. If the solver cannot
tell within a second, which can happen outside the [decidable
core](Lang/Decidability.md), the mutant is reported, with a note that it
may be equivalent. The answers about the parts combine as
`mutate::combine` says: one part that differs decides, then one that the
solver cannot tell.

```fren
pub enum Answer { Equal, Differs, Unknown }

use self::Answer::{Differs, Equal, Unknown}

pub comp combine {
    in a: Answer
    in b: Answer
    pub det out both: Answer

    ensure differs: when a = Differs or b = Differs, both = Differs
    ensure unknown: when a != Differs and b != Differs and (a = Unknown or b = Unknown), both = Unknown
    ensure equal: when a = Equal and b = Equal, both = Equal

    expect equal_only_if_both: when both = Equal, a = Equal and b = Equal
    expect differs_wins: when a = Differs, both = Differs
    cover unknown_part: both = Unknown and a = Equal
}
```

`mutate::outcome` gives what becomes of a mutant:

```fren
pub enum Outcome { Killed, Survived, Equivalent, Unviable }

use self::Outcome::{Equivalent, Killed, Survived, Unviable}

pub comp outcome {
    in viable?          -- the mutant has no static errors
    in killed?          -- some check kills it
    in equivalent?      -- the solver shows that it means what the spec means
    pub det out outcome: Outcome

    ensure unviable: unless viable?, outcome = Unviable
    ensure killed: when viable? and killed?, outcome = Killed
    ensure equivalent: when viable? and not killed? and equivalent?, outcome = Equivalent
    ensure survived: when viable? and not killed? and not equivalent?, outcome = Survived

    expect reported_unexplained: when outcome = Survived, viable? and not killed? and not equivalent?
    expect kills_win: when viable? and killed?, outcome != Equivalent
}
```

### Choosing the checker

`--by solver`, the default, checks mutants with the solver, as `fren
check` does, with `--timeout` and `--resource-limit` for each query. A query of a mutant that is
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

    ensure rule: missed? iff (by_solver? and not by_testing?)

    expect killed_by_testing: when by_testing?, not missed?
    expect killed_by_the_solver: when missed?, by_solver?
    expect missed_are_killed: when missed?, by_solver? or by_testing?
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

Each mutant is counted once, under its outcome, as `mutate::count`
says of adding one to the counts so far, so that the counts add up to the
number of mutants selected:

```fren
pub comp count {
    in outcome: Outcome
    in killed: Nat
    in survived: Nat
    in equivalent: Nat
    in unviable: Nat
    pub det out killed_after: Nat
    pub det out survived_after: Nat
    pub det out equivalent_after: Nat
    pub det out unviable_after: Nat

    ensure killed_rule: killed_after = killed + (if outcome = Killed then 1 else 0)
    ensure survived_rule: survived_after = survived + (if outcome = Survived then 1 else 0)
    ensure equivalent_rule: equivalent_after = equivalent + (if outcome = Equivalent then 1 else 0)
    ensure unviable_rule: unviable_after = unviable + (if outcome = Unviable then 1 else 0)

    expect one_more: killed_after + survived_after + equivalent_after + unviable_after
        = killed + survived + equivalent + unviable + 1
    expect killed_counted: when outcome = Killed, killed_after = killed + 1
    expect others_kept: when outcome != Survived, survived_after = survived
}
```

The kill rate is `mutate::rate`: a percentage, absent when no mutant
could be killed, that is 100 exactly when every one that could be was. The
rate divides by the number of mutants, which the solver cannot (see
[Decidability](Lang/Decidability.md)), so the component says what the
rate is like rather than how it is computed, and leaves it
undetermined:

```fren
pub comp rate {
    in killed: Nat
    in survived: Nat
    pub det out rated?      -- some mutant could be killed
    pub out rate: Nat       -- 0 when not rated

    ensure rated: rated? iff killed + survived > 0
    ensure percentage: rate <= 100
    ensure all_killed: when rated?, rate = 100 iff survived = 0
    ensure none_killed: when killed = 0, rate = 0

    expect unrated: unless rated?, rate = 0
    expect perfect_kills: when rate = 100, killed > 0 and survived = 0
    cover some_survive: rated? and 0 < rate < 100
}
```

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
    ensure as_check: code = ends.code

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
