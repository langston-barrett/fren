# Diagnostics

Fren reports two kinds of diagnostic: *static errors*, found before any
check runs, and the *results* of the [checks](Check.md). Both front ends
report the same diagnostics, with the same text, except where noted.

```fren
pub mod view
```

## Static errors

A static error is a syntax error, a name that cannot be resolved or is not
visible, a duplicate name, a type error, nonlinear arithmetic, or a
violation of a rule such as [Boolean naming](Lang/Types.md#boolean-names).
Each is an error at the offending source position. A denied
[lint](Lint.md), such as an unused import, is a
static error too. With the `fren` command, any static error means that no
check runs. In Lean, syntax and type errors
are Lean's own, and are worded differently, except for operators of other
languages (`==`, `&&`, `||`, `!`), which both front ends report with what to
write instead.

## Error codes

Every error and warning has a code, such as `F0105`, except internal
errors, which are Fren's own bugs. `fren --explain CODE` explains a code
with an erroneous example and its fix. The codes are grouped:

| Codes | About |
|---|---|
| `F01xx` | syntax |
| `F02xx` | names, modules and items |
| `F03xx` | types |
| `F04xx` | instances, and where variables may be mentioned |
| `F05xx` | traceability |
| `F06xx` | the results of checks |
| `F07xx` | lints, and setting their levels |

`view::code_group` states the grouping, for any well-formed code:

```fren
pub enum Group { Syntax, Names, Types, Instances, Traceability, Results, Lints }

pub comp code_group {
    use self::Group::{Instances, Lints, Names, Results, Syntax, Traceability, Types}
    in code: String
    pub det out group: Group

    assume well_formed: code.len = 5 and (code.starts_with?("F01") or code.starts_with?("F02")
        or code.starts_with?("F03") or code.starts_with?("F04") or code.starts_with?("F05")
        or code.starts_with?("F06") or code.starts_with?("F07"))

    req syntax_codes: when code.starts_with?("F01"), group = Syntax
    req names: when code.starts_with?("F02"), group = Names
    req types: when code.starts_with?("F03"), group = Types
    req instances: when code.starts_with?("F04"), group = Instances
    req traceability: when code.starts_with?("F05"), group = Traceability
    req results: when code.starts_with?("F06"), group = Results
    req lints: when code.starts_with?("F07"), group = Lints
}
```

The `fren` command shows the code of each diagnostic, and the messages'
notes, help and suggested edits; the Lean front end shows the same text,
without the code, with each suggested edit as a `help:` line.

## Check results

Each check yields one result for each thing it checks:

| Check | One result for each |
|---|---|
| Realizability | component |
| Expectations | expectation |
| Instance assumptions | instance and assumption of the instantiated component |
| Vacuity | requirement or expectation with a trigger |
| Redundancy | assumption and requirement |
| Determinism | `det out` |

A passing result is silent. A failing result is an error, except that a
redundant constraint is a warning. An inconclusive result is a warning. A
failure is reported at:

| Failure | Position | Details |
|---|---|---|
| Unrealizable | the component's name | the input, a note at each conflicting requirement |
| Contradictory assumptions | the component's name | the contradictory assumptions |
| Expectation does not hold | the expectation's name | a counterexample: the inputs and public outputs |
| Instance assumption may not hold | the instance's name | a counterexample: the inputs and earlier instances' public outputs |
| Vacuous | the constraint's trigger | the assumptions and requirements that rule it out |
| Redundant | the constraint's name | the constraints it follows from |
| Not determined | the output's name | an input, and two values of the output for it |

A counterexample in a spec with [functions](Lang/Items.md#functions) also
gives the value of each application in the constraints it is about, at the
counterexample's arguments, such as `ends_in_q?(name) = true`: these are the
part of the model's [interpretation](Check.md#interpretations) that the
failure depends on. A value of an [abstract type](Lang/Types.md#abstract-types)
is shown as the type's name, `#` and a number, such as `Name#0`: within one
counterexample, two values are shown alike exactly when they are equal.

A value of an enumeration or a record is shown as Fren would build it:
`Shape::Circle(2)`, `List::Cons(1, List::Nil)` or `Point { x := 1, y := 2 }`,
with the enumeration's or record's name and not its module, as for a
variant without a payload.

An inconclusive result is reported at the position of the corresponding
failure, saying what could not be decided and why. What it advises
depends on whether the component is in the [decidable
core](Lang/Decidability.md): if it is, the solver ran out of time, so the
advice is to raise the time limit; if some construct of it opted out of
the core, the solver may have given up, so the advice names that.
`view::inconclusive_advice` states this:

```fren
pub enum Advice { RaiseTimeout, NamesConstructs }

pub comp inconclusive_advice {
    in decidable?            -- no construct of the component is outside the core
    pub det out advice: Advice

    req rule: advice = (if decidable? then Advice::RaiseTimeout else Advice::NamesConstructs)
}
```

After the results, a summary is reported as information. It counts the
results by verdict, except that redundant constraints, which are warnings,
are counted apart from the other failures:

```
fren: 6 passed, 0 failed, 0 inconclusive, 0 redundant
```

If some passes came from [checks by testing](Check.md#checking-by-testing),
the summary says how many, after the passes: `fren: 6 passed (2 by
testing), ...`.

## Severity

In Lean, an error fails `lake build`, and a warning fails `lake build
--wfail`, so severities do for a Lean build what [exit
statuses](Cli.md#exit-status) do for the `fren` command.

`view::severity` gives the severity of a result from its check and
verdict:

```fren
pub enum Severity { Silent, Info, Warning, Error }

use check::{Kind, Verdict}
use check::Kind::Redundancy
use check::Verdict::{Fail, Inconclusive, Pass}
use self::Severity::{Error, Info, Silent, Warning}

pub comp severity {
    in kind: Kind
    in verdict: Verdict
    pub det out level: Severity

    req pass: when verdict = Pass, level = Silent
    req fail: when verdict = Fail and kind != Redundancy, level = Error
    req redundant: when verdict = Fail and kind = Redundancy, level = Warning
    req inconclusive: when verdict = Inconclusive, level = Warning

    expect only_passes_are_silent: when level = Silent, verdict = Pass
    expect errors_are_failures: when level = Error, verdict = Fail
    expect results_are_not_info: level != Info
}
```

`view::build` states when a Lean build fails, from the most severe level of
the results of a `#fren_check`:

```fren
pub comp build {
    in worst: Severity
    pub det out fails?     -- `lake build` fails
    pub det out fails_wfail?  -- `lake build --wfail` fails

    req errors: fails? iff worst = Error
    req warnings: fails_wfail? iff (worst = Error or worst = Warning)

    expect wfail_is_stricter: when fails?, fails_wfail?
}
```

`view::summary` states that the summary is information, whatever the
counts:

```fren
pub comp summary {
    in n_pass: Int
    in n_fail: Int
    in n_inconclusive: Int
    in n_redundant: Int    -- redundant constraints, not counted as failed
    pub det out level: Severity

    assume counts: n_pass >= 0 and n_fail >= 0 and n_inconclusive >= 0 and n_redundant >= 0

    req always_info: level = Info
}
```

`view::counted` says which count a result is in: by its verdict, except
that a redundant constraint is counted apart. So the failures that the
summary counts are exactly the results that are errors:

```fren
pub enum Bucket { Passed, Failed, InconclusiveBucket, RedundantBucket }

pub comp counted {
    use self::Bucket::{Failed, InconclusiveBucket, Passed, RedundantBucket}
    in kind: Kind
    in verdict: Verdict
    pub det out bucket: Bucket

    req redundant: when kind = Redundancy and verdict = Fail, bucket = RedundantBucket
    req by_verdict: unless kind = Redundancy and verdict = Fail,
        bucket = (if verdict = Pass then Passed else if verdict = Fail then Failed else InconclusiveBucket)
}

expect failures_are_errors: forall (c: counted) (s: severity),
    when c.kind = s.kind and c.verdict = s.verdict,
    c.bucket = Bucket::Failed iff s.level = Error

#fren_check
```
