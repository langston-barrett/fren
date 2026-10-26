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
more. Lean goes on only after the item with the parse error: what its
parser recovers of that item is not elaborated, so its parse error is all
that is reported about it, and it neither declares nor uses a name. In Lean, the static errors are those before the `#fren_check`, in
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
6. each assumption, guarantee and expectation, in order.

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
`constant_output`, `definable_output` and `case_split_guarantees`, and its
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

    assume well_formed: code.len = 5 and (code.starts_with?("F01") or code.starts_with?("F02")
        or code.starts_with?("F03") or code.starts_with?("F04") or code.starts_with?("F05")
        or code.starts_with?("F06") or code.starts_with?("F07") or code.starts_with?("F08"))
    pub det out group: Group

    ensure syntax_codes: when code.starts_with?("F01"), group = Syntax
    ensure names: when code.starts_with?("F02"), group = Names
    ensure types: when code.starts_with?("F03"), group = Types
    ensure instances: when code.starts_with?("F04"), group = Instances
    ensure traceability: when code.starts_with?("F05"), group = Traceability
    ensure results: when code.starts_with?("F06"), group = Results
    ensure lints: when code.starts_with?("F07") or code.starts_with?("F08"), group = Lints

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
| Realizability | component, and contract of an uninterpreted function with postconditions |
| Expectations | expectation |
| Cover goals | cover goal |
| Instance assumptions | instance and assumption of the instantiated component |
| Vacuity | guarantee or expectation with a trigger |
| Redundancy | assumption and guarantee |
| Determinism | `det out` |
| Definedness | index |
| Completeness | table without a `_` row, and `match` whose arms without guards are not exhaustive |
| Disjointness | two rows of a table, other than `_` |
| Preconditions | application and precondition of the applied function |
| Postconditions | postcondition of a defined function |
| Reachability | arm of a `match` that has a guard or follows one, and row of a table but its only row `_` |

A passing result is silent, except that a passing cover goal shows its
witness (see below). A failing result is an error, except that a
redundant constraint is a warning. An inconclusive result is a warning. A
failure is reported at:

| Failure | Position | Details |
|---|---|---|
| Unrealizable | the component's name | a note: the input, one variable to a line, and the guarantees that conflict on it; and a note at each of those: the output that it forces to a value that the others rule out, for at most `--examples` of them, else whom it conflicts with |
| Contradictory assumptions | the component's name | the contradictory assumptions |
| Expectation does not hold | the expectation's name | a counterexample: the inputs and public outputs |
| Cover goal cannot be met | the goal's name | the assumptions and guarantees that rule it out |
| Instance assumption may not hold | the instance's name | a counterexample: the inputs and earlier instances' public outputs |
| Vacuous | the constraint's trigger | the assumptions and guarantees that rule it out |
| Redundant | the constraint's name | the constraints it follows from |
| Not determined | the output's name | an input, and two values of the output for it |
| Index may be out of range | the index's `[` | a counterexample: the public variables |
| Table may have no row that holds | the table's `table` | a counterexample: the public variables, for which no row holds |
| Rows may both hold | the later row's condition | the two rows, by their numbers from 1, and a witness: the public variables, for which both hold |
| Precondition may not hold | the applied function's name | the precondition, and a counterexample: the public variables |
| Postcondition does not hold | the postcondition's name | a counterexample: the function's parameters |
| Postconditions cannot all hold | the function's name | a note: the arguments, one to a line, and the postconditions that conflict on them; and a note at each of those: the value of the function that it forces to one that the others rule out, for at most `--examples` of them, else whom it conflicts with |
| Contradictory preconditions | the function's name | the contradictory preconditions |
| `match` may have no arm that is taken | the `match`'s `match` | a counterexample: the public variables, for which no arm is taken |
| Arm never taken | the arm's pattern | the arm, by its number from 1 |
| Row never the first that holds | the row's condition, or its `_` | the row, by its number from 1 |

A passing [cover goal](Check.md#cover-goals) is reported with its
witness, the behaviour in which it holds, as a note at the goal's name:
the inputs and public outputs, shown as a counterexample shows them. The
note is information, like the notes at the guarantees of an
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
assumptions and guarantees, each instance's bindings and the meaning of
its component (its assumptions, guarantees, definitions and instances,
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

An unrealizable component's error has a note that spans several lines:
`for the input`, then each variable of the input and its value, one to a
line and indented, and then the guarantees that conflict on it, in their
order, named as a list (`` `a` ``, `` `a` and `b` ``, `` `a`, `b` and `c` ``).
Each line of a note after its first is indented under the text after
`note: `, in both front ends. An input with no variables has no lines of
its own: the note is then `note: no outputs satisfy ...`. A failure of an
uninterpreted function's postconditions has the same note, with `for the
arguments` and `no value of `f` satisfies`.

Each guarantee of the conflict has one note, information at its name,
so that an editor marks every one. A guarantee that
[forces](Check.md#forced-outputs) an output has a clash note: the
guarantee and what it forces, and then the other guarantees of the
conflict, named as a list, and what they force, with `forces` after one
guarantee and `force` after more. A whole value `v` of the output `o` is
`o = v`. A variant is the pattern test `o is P`, where `P` is the pattern
that exactly the variant's values match: `E::C(_)`, with a `_` for each
value of the payload, as in `E::C(_, _)`, or `E::C` for a variant without
a payload. A variant without a payload has one value, so a side that
forces it forces that value, and the note gives it as `o = E::C`. Any other guarantee
has `conflicts with` and the other guarantees, named as a list, or, in a
conflict of one guarantee, `is false for this input`; neither repeats the
input, which the error's note gives. `view::wildcards` states the `_`s of
a payload of `arity` values: `_`, and then `, _` for each further value,
which is all that is left of `text` once each `, _` is removed. Replacing
in a string is outside the decidable core, though the solver decides
these:

```fren
-- `replace_all` is outside the decidable core, and no other method states the shape.
set_option fren.lint.undecidable "allow" in
pub comp wildcards {
    in arity: Nat
    in text: String   -- the wildcards
    pub det out shaped? := (if arity = 0 then text = ""
        else text.starts_with?("_") and text.len = 3 * arity - 2 and text.replace_all(", _", "") = "_")

    expect two: when arity = 2 and text = "_, _", shaped?
    expect not_three: when arity = 3 and text = "_, _", not shaped?
}
```

`view::clash_text` states the clash note, where each side is a `Forced`,
with its wildcards, `blanks`, which `view::wildcards` shapes for a
variant's arity. Concatenating within a `match` is outside the decidable
core too:

```fren
-- What a clash note says a side forces: a whole value, as Fren writes it,
-- or a variant, as Fren names it (`E::C`), with how many values its payload has.
pub enum Forced { Value(String), Variant(String, Nat) }

-- `++` in a `match` arm makes a word equation; flattening `Forced` into flags would avoid it.
set_option fren.lint.undecidable "allow" in
pub comp clash_text {
    in guarantee: String     -- the guarantee's name
    in output: String        -- the output's name
    in forced: Forced        -- what the guarantee forces of the output
    in blanks: String        -- the wildcards of its variant, if it is one
    in others: String        -- the other guarantees of the conflict, named as a list
    in count: Int            -- how many others there are
    in other_forced: Forced  -- what they force of the output
    in other_blanks: String  -- the wildcards of its variant, if it is one

    assume some_other: count >= 1
    pub out said: String := match forced {   -- what the guarantee forces, as the note says it
        Forced::Value(v) => output ++ " = " ++ v,
        Forced::Variant(c, n) => output ++ " is " ++ c ++ (if n = 0 then "" else "(" ++ blanks ++ ")"),
    }
    pub out other_said: String := match other_forced {   -- what the others force
        Forced::Value(v) => output ++ " = " ++ v,
        Forced::Variant(c, n) => output ++ " is " ++ c ++ (if n = 0 then "" else "(" ++ other_blanks ++ ")"),
    }
    pub out text: String := "`" ++ guarantee ++ "` forces " ++ said ++ ", but " ++ others
        ++ (if count = 1 then " forces " else " force ") ++ other_said

    expect one_other: when guarantee = "low" and output = "y" and forced = Forced::Value("0") and others = "`high`"
        and count = 1 and other_forced = Forced::Value("1"), text = "`low` forces y = 0, but `high` forces y = 1"
    expect variant: when guarantee = "t" and output = "d" and forced = Forced::Variant("D::R", 1) and blanks = "_"
        and others = "`h`" and count = 1 and other_forced = Forced::Value("D::G"),
        text = "`t` forces d is D::R(_), but `h` forces d = D::G"
}
```

For example, with `--examples 1`, the default:

```text
error[F0601]: `http::retry` is not realizable
 --> retry.fren:9:6
  |
9 | comp retry {
  |      ^^^^^ not realizable
  |
  = note: for the input
              method = Method::Get
              status = 429
              attempt = 4
              retry_after = Seconds(31)
          no outputs satisfy `transient`, `honor_server` and `latency_budget`
  = help: weaken one of them, or add an `assume` that rules this input out

note: `transient` forces retry? = true, but `honor_server` and `latency_budget` force retry? = false
  --> retry.fren:19:12
   |
19 |     ensure transient: retry? iff (status = 429 or status = 503)
   |            ^^^^^^^^^

note: conflicts with `transient` and `latency_budget`
  --> retry.fren:21:12
   |
21 |     ensure honor_server: when retry?, delay >= retry_after
   |            ^^^^^^^^^^^^

note: conflicts with `transient` and `honor_server`
  --> retry.fren:23:12
   |
23 |     ensure latency_budget: delay <= MAX_DELAY
   |            ^^^^^^^^^^^^^^
```

A counterexample, or a witness, gives the values of the variables that
the check's [query](Check.md) mentions, those that occur in one of its
formulas, and of no others: a variable that none mentions could have any
value, so showing one would say nothing. That a `Nat` variable is at least
0 is one of the formulas (see [Natural numbers](Lang/Types.md#natural-numbers)),
so a `Nat` is shown even when nothing else mentions it. In

```text
comp c { in a: Int in b: Int pub out p? ensure r: p? iff a > 0 expect e: p? }
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

    ensure rule: advice = (if decidable? then Advice::RaiseTimeout else Advice::NamesConstructs)
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

    ensure pass: when verdict = Pass, level = Silent
    ensure fail: when verdict = Fail and kind != Redundancy, level = Error
    ensure redundant: when verdict = Fail and kind = Redundancy, level = Warning
    ensure inconclusive: when verdict = Inconclusive, level = Warning

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

    ensure errors: fails? iff worst = Error
    ensure warnings: fails_wfail? iff worst >= Warning

    expect wfail_is_stricter: when fails?, fails_wfail?
}
```

`view::summary` states that the summary is information, whatever the
counts, so it has none as inputs:

```fren
pub comp summary {
    pub det out level: Severity

    ensure always_info: level = Info
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

    ensure redundant: when kind = Redundancy and verdict = Fail, bucket = Redundant
    ensure by_verdict: unless kind = Redundancy and verdict = Fail,
        bucket = (if verdict = Pass then Passed else if verdict = Fail then Failed else InconclusiveBucket)
}

expect failures_are_errors: forall (c: counted) (s: severity),
    when c.kind = s.kind and c.verdict = s.verdict,
    c.bucket = Bucket::Failed iff s.level = Error

#fren_check
```
