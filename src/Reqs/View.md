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
[lint](Lint.md), such as an unused import, is a static error too. Both
front ends report each static error with the same words, at the same
position, except syntax errors. In Lean those are reported by Lean's
parser, in its own words, though both front ends report the operators of
other languages (`==`, `&&`, `||`, `!`) alike, with what to write instead.

Any static error means that no check runs, with either front end: instead
of the checks' results and summary, the `fren` command ends with `could
not check due to previous errors`, with no location, and Lean's
`#fren_check` reports the same. The errors are not counted, since the
`fren` command stops at a parse error, where Lean goes on and may find
more. In Lean, the static errors are those before the `#fren_check`, in
any file: those of Fren's items, of `#fren_check`s (but not their
checks'), and of `set_option`s of lints and evidence claims; Lean's parse
errors, which it finds by parsing the file again with the syntax in scope
at the `#fren_check`; and the lints so far that are errors. The errors of
what only Lean reads, `impl`, `interp` and `#fren_trace`, do not count.
Nor do the errors inside a `#guard_msgs`, expected or not, so that a Lean
test can show an error and then the checks: an unexpected one fails the
`#guard_msgs` itself. An item where `undecidable` is denied is still not
checked ([Decidability lints](Lint/Decidability.md#undecidable-constructs)).

### How many are reported

In a component, the parts below are checked on their own, in this order,
and each reports its first static error; an error in one does not stop the
others:

1. its name, and that its members' names are distinct: an error here stops
   the component;
2. each variable's declaration: its name, then its type (an error in its
   name, such as in [shadowing](Lang/Components.md#shadowing), still
   leaves its type to be checked); then one cycle of definitions, if any;
3. each instance: its name, then its component and the names it binds;
4. the bindings of each instance, together;
5. each definition, each after those it mentions;
6. each assumption, requirement and expectation, in order.

An error that would only follow from an earlier one is not reported. After
an error in a variable's declaration or in an instance, the component
stops once the parts of the same step are checked, at the end of step 2
or step 3, since what mentions the variable or the instance would only
repeat it; a cycle of definitions stops it at the end of step 2 too: so an instance whose component cannot be found, or has a static error
itself, is reported once, at the instance, and not at each use. A
definition, or an instance's bindings, with an error still declare their
variable, with its declared type, so what mentions them is checked as
usual, and reports only its own errors.

Any other item, including a global expectation and a refinement (whose
bindings are checked together), reports its first static error only. A
component or other item with a static error is not checked.

An item with a static error still reports its [lints](Lint.md), with
either front end: those found in each part before its error. A part checks
its constructs before their operands, so an error in an operand does not
hide them: a set literal, `in`, `union`, `inter`, `minus` and `subset`, and
membership in a set of one member; a method call is checked after it is
typed, and a constraint's name before its `?` error. A component with an
error in its members (after step 1 above) still reports
`constant_output`, `definable_output` and `case_split_reqs`, and its
declaration and line lints (`many_single_char_names`, `similar_names` and
`too_many_lines`), but not `unused_variables`, which needs all of it. What
it used before the error counts for the lints of the file, such as an
unused import or dead code.

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
| `F08xx` | more lints, once `F07xx` is full |

`view::code_group` states the grouping, for any well-formed code:

```fren
pub enum Group { Syntax, Names, Types, Instances, Traceability, Results, Lints }

pub comp code_group {
    use self::Group::{Instances, Lints, Names, Results, Syntax, Traceability, Types}
    in code: String
    pub det out group: Group

    assume well_formed: code.len = 5 and (code.starts_with?("F01") or code.starts_with?("F02")
        or code.starts_with?("F03") or code.starts_with?("F04") or code.starts_with?("F05")
        or code.starts_with?("F06") or code.starts_with?("F07") or code.starts_with?("F08"))

    req syntax_codes: when code.starts_with?("F01"), group = Syntax
    req names: when code.starts_with?("F02"), group = Names
    req types: when code.starts_with?("F03"), group = Types
    req instances: when code.starts_with?("F04"), group = Instances
    req traceability: when code.starts_with?("F05"), group = Traceability
    req results: when code.starts_with?("F06"), group = Results
    req lints: when code.starts_with?("F07") or code.starts_with?("F08"), group = Lints

    expect syntax_example: when code = "F0105", group = Syntax
    expect lints_example: when code = "F0721", group = Lints
    expect more_lints: when code = "F0801", group = Lints
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
| Cover goals | cover goal |
| Instance assumptions | instance and assumption of the instantiated component |
| Vacuity | requirement or expectation with a trigger |
| Redundancy | assumption and requirement |
| Determinism | `det out` |
| Definedness | index |
| Completeness | table without a `_` row |
| Disjointness | two rows of a table, other than `_` |

A passing result is silent, except that a passing cover goal shows its
witness (see below). A failing result is an error, except that a
redundant constraint is a warning. An inconclusive result is a warning. A
failure is reported at:

| Failure | Position | Details |
|---|---|---|
| Unrealizable | the component's name | the input, a note at each conflicting requirement |
| Contradictory assumptions | the component's name | the contradictory assumptions |
| Expectation does not hold | the expectation's name | a counterexample: the inputs and public outputs |
| Cover goal cannot be met | the goal's name | the assumptions and requirements that rule it out |
| Instance assumption may not hold | the instance's name | a counterexample: the inputs and earlier instances' public outputs |
| Vacuous | the constraint's trigger | the assumptions and requirements that rule it out |
| Redundant | the constraint's name | the constraints it follows from |
| Not determined | the output's name | an input, and two values of the output for it |
| Index may be out of range | the index's `[` | a counterexample: the public variables |
| Table may have no row that holds | the table's `table` | a counterexample: the public variables, for which no row holds |
| Rows may both hold | the later row's condition | the two rows, by their numbers from 1, and a witness: the public variables, for which both hold |

A passing [cover goal](Check.md#cover-goals) is reported with its
witness, the behaviour in which it holds, as a note at the goal's name:
the inputs and public outputs, shown as a counterexample shows them. The
note is information, like the notes at the requirements of an
unrealizable component: the result itself is silent, so the note changes
neither the summary's counts nor the exit status. A witness's values
are not shown, and the note says so instead, when they depend on an
[interpretation](Lang/Components.md#interpretations), which the note
cannot show: when some variable of the component, its own or an
instance's, has a type that is or contains an [abstract
type](Lang/Types.md#abstract-types), or when a formula of the goal's
[query](Check.md#cover-goals) uses an abstract type or an [uninterpreted
function](Lang/Items.md#uninterpreted-functions), directly or through a
defined function. Those formulas are the component's definitions,
assumptions and requirements, each instance's bindings and the meaning of
its component (its assumptions, requirements, definitions and instances,
recursively), and the goal; no expectation or other cover goal is among
them. Both front ends decide this by the same rule, and the Lean front
end cannot read every such model.

```text
note: cover goal `heater::overheat` is met
 --> heater.fren:7:11
  |
7 |     cover overheat: temp > 100 and alarm?
  |           ^^^^^^^^ met
  |
  = witness: temp = 101, alarm? = true
```

A counterexample, or a witness, gives the values of the variables that
the check's [query](Check.md) mentions, those that occur in one of its
formulas, and of no others: a variable that none mentions could have any
value, so showing one would say nothing. That a `Nat` variable is at least
0 is one of the formulas (see [Natural numbers](Lang/Types.md#natural-numbers)),
so a `Nat` is shown even when nothing else mentions it. In

```text
comp c { in a: Int in b: Int pub out p? req r: p? iff a > 0 expect e: p? }
```

the counterexample of `e` is `a = 0, p? = false`, without `b`. Both front
ends show the same variables.

A counterexample, or a witness, in a spec with [functions](Lang/Items.md#functions) also
gives the value of each application in the constraints it is about, at the
counterexample's arguments, such as `ends_in_q?(name) = true`: these are the
part of the model's [interpretation](Check.md#interpretations) that the
failure depends on. A value of an [abstract type](Lang/Types.md#abstract-types)
is shown as the type's name, `#` and a number, such as `Name#0`: within one
counterexample, two values are shown alike exactly when they are equal.

A value of an enumeration or a record is shown as Fren would build it:
`Shape::Circle(2)`, `List::Cons(1, List::Nil)` or `Point { x := 1, y := 2 }`,
with the enumeration's or record's name and not its module, as for a
variant without a payload. So is a value of a newtype, as in `Ms(5)`, even
though the solver sees only its underlying type's value.

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

The severities are ordered from the least severe to the most.
`view::severity` gives the severity of a result from its check and
verdict:

```fren
pub ordered enum Severity { Silent, Info, Warning, Error }

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
    req warnings: fails_wfail? iff worst >= Warning

    expect wfail_is_stricter: when fails?, fails_wfail?
}
```

`view::summary` states that the summary is information, whatever the
counts, so it has none as inputs:

```fren
pub comp summary {
    pub det out level: Severity

    req always_info: level = Info
}
```

`view::counted` says which count a result is in: by its verdict, except
that a redundant constraint is counted apart. So the failures that the
summary counts are exactly the results that are errors. `InconclusiveBucket`
is named apart from the verdict `Inconclusive`, and `RedundantBucket` like
it, so `Bucket` allows `enum_variant_names`, which fires on a variant that
contains its enumeration's name:

```fren
-- `Inconclusive` is a verdict's name, which `counted` uses too, so the
-- bucket's has a suffix.
set_option fren.lint.enum_variant_names "allow" in
pub enum Bucket { Passed, Failed, InconclusiveBucket, Redundant }

pub comp counted {
    use self::Bucket::{Failed, InconclusiveBucket, Passed, Redundant}
    in kind: Kind
    in verdict: Verdict
    pub det out bucket: Bucket

    req redundant: when kind = Redundancy and verdict = Fail, bucket = Redundant
    req by_verdict: unless kind = Redundancy and verdict = Fail,
        bucket = (if verdict = Pass then Passed else if verdict = Fail then Failed else InconclusiveBucket)
}

expect failures_are_errors: forall (c: counted) (s: severity),
    when c.kind = s.kind and c.verdict = s.verdict,
    c.bucket = Bucket::Failed iff s.level = Error

#fren_check
```
