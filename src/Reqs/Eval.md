# Evaluation and testing

```
fren eval --comp PATH [--set VAR=VALUE]... [--seed N] [-A|-W|-D|-F LINT]... FILE...
fren quickcheck [--tests N] [--seed N] [-A|-W|-D|-F LINT]... FILE...
```

The [checks](Check.md) ask a solver about every behaviour of a component
at once. Fren can also evaluate a spec on one behaviour at a time, without
the solver: `fren eval` evaluates the constraints of a component on a
behaviour, and `fren quickcheck` tests a spec on random behaviours, as
Cryptol's `:check` does, before the solver is asked anything. The same
evaluator confirms each model that the solver returns to `fren check` (see
[Confirming models](#confirming-models)).

```fren
pub mod eval

use check::{Kind, Verdict}
use check::Verdict::{Fail, Inconclusive, Pass}
```

## Behaviours

A *behaviour* of a component is an
[interpretation](Lang/Components.md#interpretations), together with a value
for each of the component's variables: its inputs and outputs, and the
variables of its instances, including those that are hidden (see
[Instances](Lang/Instances.md#instance-variables)). A behaviour of a
[global expectation](Lang/Global.md) is a behaviour of each of its
binders, all under one interpretation.

In a behaviour, every constraint is `true` or `false`, by the meaning of
its [expression](Lang/Expressions.md). The evaluator computes the value of
each [constant](Lang/Items.md#constants) once, when it reads the spec,
without an interpretation. A constant whose value then reads an index out
of range, or a table or `match` where no row or arm is taken, is kept as its
expression: in each behaviour, it has the value that the interpretation
gives the table or `match`, and none for the index; its indexes, tables
and `match`es are the constant's own, which the checks ask about at the constant, not
where it is mentioned. A constant whose value cannot be computed for any
other reason is an internal error. The evaluator computes it from the
spec itself, not from the formulas given to the solver, so it is an
independent statement of what a spec means. A name of a
[`let` or `where`](Lang/Let.md) is read as its definition, so it is not
part of a behaviour, and counterexamples show variables only. In the notation of
[Components](Lang/Components.md#meaning), a behaviour is *admissible* if
`A` and `I` hold in it, and it *meets* the component if `R` holds as well.
`eval::status` gives the status of a behaviour:

```fren
pub enum Status { Inadmissible, Violates, Meets }

use self::Status::{Inadmissible, Meets, Violates}

pub comp status {
    in assumes?          -- every assumption holds
    in insts?            -- every instance's constraint `I_w` holds
    in guarantees?      -- every guarantee holds
    pub det out status: Status

    ensure inadmissible: unless assumes? and insts?, status = Inadmissible
    ensure violates: when assumes? and insts? and not guarantees?, status = Violates
    ensure meets: when assumes? and insts? and guarantees?, status = Meets

    expect meets_all: when status = Meets, assumes? and insts? and guarantees?
}
```

## Values

A value is written as a [counterexample](View.md#check-results) shows it:
`true` or `false`, an integer such as `-3`, a string literal such as
`"a\n"`, a variant such as
`Mode::Heat` or `Shape::Circle(2)`, a record such as `Point { x := 1, y :=
2 }`, a newtype's value such as `Ms(5)`, a set such as `{1, 2}`, a relation such as `{(1, "a"), (2, "b")}`, a
sequence such as `[1, 2]`, or,
for an [abstract type](Lang/Types.md#abstract-types), the type's
name, `#` and a number, such as `Name#0`. Within one behaviour, two values
of an abstract type written alike are equal, and two written differently
are not.

## Searching for behaviours

Both commands search for behaviours. The search chooses the variables in
order: the inputs, then the [defined
outputs](Lang/Components.md#defined-outputs) whose definitions mention
only inputs and such outputs, computed from them, then each instance's
variables, the instance's inputs being its bindings' values, then the
other outputs. It tries each variable's
candidates in a random order, and backtracks when a constraint that can
already be evaluated is false. A variable's candidates are:

- both `Bool`s, and each variant of an enumeration, with a payload built
  from the candidates of its types, to a bounded depth;
- for an `Int`, small integers, the integer literals and constants of the
  component, its expectations included, and their neighbours, random integers, and the value of
  any expression that a constraint equates the variable with, such as `x
  + 1` in `y = x + 1`;
- for a `Nat`, those of an `Int` that are at least 0;
- for an abstract type `T`, `T#0` up to a random bound;
- for a `String`, `""`, `"a"` and `"b"`; the string literals and constants
  of the component, its expectations included, each also with `"a"` before
  and after it, and, for those of up to six characters, what remains after
  each of their first characters, such as the `:*` of `::*`, so that
  `s.contains?("..")` and `s.starts_with?("x")` have strings that satisfy
  them; a few random strings that match each pattern of a `matches?` in
  the component, each also followed by `"a"`; and the value of any
  expression that a constraint equates the variable with;
- for a `Set(T)`, the empty set and singletons of the candidates of `T`,
  and the value of any expression that a constraint equates the variable
  with;
- for a `Seq(T)`, the empty sequence, and sequences of one and two of the
  candidates of `T`; for each integer candidate from 3 to 4, such as the
  `3` of `q.len = 3`, a few random sequences of that length; and the value
  of any expression that a constraint equates the variable with. An index
  out of range has no value that the evaluator knows, since it is part of
  the interpretation;
- for a `Rel(A, B)`, the empty relation, single pairs of candidates of `A`
  and `B`, and, if `A` is `B`, a chain of two pairs, so that `closure` has
  something to close.

The interpretation is chosen at random: each function's value at each
argument is random, but the same wherever it is applied in the behaviour,
and at least 0 if its result is a `Nat`. Where the arguments meet the
function's [preconditions](Lang/Items.md#contracts), the value is the first
of a few random values that meets its postconditions; if none does, the
application has no value that the evaluator knows, as an index out of
range has none, since a value that does not meet them is no
interpretation of the spec. So is the value of each type that
a [table](Lang/Expressions.md#tables) without a `_` row has where no row
holds, and a [`match`](Lang/Expressions.md#matches) where no arm is taken,
which the interpretation gives, as the solver's does: one value of
each type, the same for every such table and `match`.

The search may miss a behaviour that exists, since it tries only some
values, but every behaviour it reports is genuine: it is a behaviour of the
component, with the status that the evaluator gives it.

## `fren eval`

`fren eval --comp PATH FILE...` evaluates a behaviour of the component
`PATH` of the spec in the files. `--set x=VALUE` gives the variable `x` a
value, as does `--set w.x=VALUE` for a variable of the instance `w`.
`VALUE` is typed as a binding of `x` would be: a `Nat` is widened to an
`Int`, and an `Int`, such as `5 - 3`, is not accepted for a `Nat`. The
variables that are not set, and the interpretation, are chosen by
[searching](#searching-for-behaviours) for a behaviour that meets the
component, starting from `--seed` (default 0). If the search finds none,
the variables not set have no value, and nor does any constraint that
depends on them.

The command writes to standard output the value of each variable and of
each constraint (`true`, `false` or `unknown`), and the behaviour's
status. A value that is not of its variable's type, or a variable that
the component does not have, is an error in the arguments.
`eval::eval_exit` gives the exit status:

```fren
pub comp eval_exit {
    in ran?              -- the spec and the arguments have no errors
    in complete?         -- every variable has a value
    in status: Status
    in expect_false?     -- some expectation is false
    pub det out code: Int

    ensure not_run: unless ran?, code = 2
    ensure incomplete: when ran? and not complete?, code = 3
    ensure fails: when ran? and complete? and (status != Meets or expect_false?), code = 1
    ensure passes: when ran? and complete? and status = Meets and not expect_false?, code = 0

    expect zero_means_met: when code = 0, status = Meets and not expect_false?
}

use cli::exit_status

refine eval_exit_status: eval_exit refines exit_status
```

## `fren quickcheck`

`fren quickcheck FILE...` tests every component, global expectation and
[refinement](Lang/Refinement.md) of the spec on random behaviours: a
refinement as the component that checks it, for the checks that run on it. For each, it runs `--tests` tests (default
100), starting from `--seed` (default 0), so a run can be repeated. Each
test chooses a random interpretation and searches for an admissible input.
For each instance in turn, it confirms the instance's assumptions on the
instance's inputs, then searches for the instance's behaviour. Last, it
searches for outputs that meet the component. A global expectation's
test searches for a behaviour that meets each binder's component.

Testing reports what it finds as the checks report it, at the same
positions (see [Check results](View.md#check-results)):

| Check | Testing reports |
|---|---|
| Expectations | a behaviour that meets the component, in which the expectation is false |
| Cover goals | a behaviour that meets the component, in which the goal holds: a witness, which passes it |
| Global expectations | behaviours of the binders in which the body is false |
| Instance assumptions | an admissible input, with behaviours of the earlier instances, on which an assumption of the instance's component is false |
| Determinism | two behaviours on the same input, with different values of the `det out` |
| Realizability | an admissible input, with behaviours of the instances, for which the search found no outputs |

Vacuity and redundancy are not tested: they ask whether something can
hold at all, which a failed search does not refute. A [cover
goal](Check.md#cover-goals) asks that too, but a behaviour found shows
that it can hold, so testing passes a goal for which it finds a witness,
and never fails one. Nor are definedness,
completeness, disjointness and reachability (see [Checking by
testing](Check.md#checking-by-testing)).

A test *reaches* a check when it finds what the check is about, as in the
table: a behaviour that meets the component, for an expectation; an
admissible input with behaviours of the earlier instances, for an
instance assumption; and so on. For an expectation, a global expectation
or an instance assumption with a [trigger](Lang/Components.md#triggers),
the trigger must also hold: where it is false, the constraint holds by its
trigger alone, so the test says nothing about it. Since a random behaviour
seldom satisfies a narrow trigger, testing searches for one that does:

- for an expectation with a trigger, each test whose behaviour does not
  reach it searches again, from a new input, for a behaviour that meets the
  component and in which the trigger holds;
- a global expectation's test searches for behaviours of the binders in
  which the body's trigger holds;
- for a cover goal without a witness yet, each test searches, from a new
  input, for a behaviour that meets the component and in which the goal
  holds. A cover goal is reached by a test that finds a witness: it is
  `reaches` with the goal as its trigger.

Testing also searches for counterexamples directly: for an expectation or
a global expectation not yet refuted, each test that finds what the
expectation is about (a behaviour that meets the component, or behaviours
of the binders in which the body's trigger holds, if it has one) also
searches for one in which it is false. Backtracking then tries combinations of candidates that random
behaviours seldom reach, such as a lexeme and the input after it that
together refute a rule about both. A behaviour found is a counterexample;
none found says nothing.

So a trigger that no search satisfies costs one more search in each test,
for each expectation that has it, and each expectation not yet refuted
costs one more, the direct search for a counterexample. An instance
assumption's trigger gets no such search: it is about an instance's
inputs, which its bindings give.

`eval::reaches` states when a test reaches a check:

```fren
pub comp reaches {
    in found?            -- the test found what the check is about
    in has_trigger?
    in trigger?          -- the trigger holds in what the test found
    pub det out reached?

    ensure rule: reached? iff (found? and (not has_trigger? or trigger?))

    expect false_trigger_never: when has_trigger? and not trigger?, not reached?
}
```

A counterexample from testing is genuine, so it fails the check. But
the search can miss outputs, so an input for which none were found
suggests that the component is not realizable, without showing it. That
gives a warning, `F0609`, and an inconclusive result. A check that no test
reached, because no admissible behaviour was found, is also inconclusive,
with the warning `F0610`. A check with a trigger that no test reached,
though some found what it is about, is inconclusive with the warning
`F0612`, at the check, unless the component already has `F0610`. A
cover goal for which no test found a witness, though some found a
behaviour that meets the component, is inconclusive with the warning
`F0616`, at the goal, likewise. `eval::test_verdict` gives the verdict of testing one
check, from whether some test refuted it and how many tests reached it:

```fren
pub comp test_verdict {
    in kind: Kind
    in refuted?          -- some test is a counterexample, or an input without outputs
    in n_tests: Nat      -- the tests that reached the check (`reaches`)
    pub det out verdict: Verdict

    assume testable: kind != Kind::Vacuity and kind != Kind::Redundancy
    -- A cover goal is reached by its witnesses, which refute nothing.
    assume witnesses: when kind = Kind::Cover, not refuted?

    ensure definite: when refuted? and kind != Kind::Realizability, verdict = Fail
    ensure not_found: when refuted? and kind = Kind::Realizability, verdict = Inconclusive
    ensure passes: when not refuted? and n_tests > 0, verdict = Pass
    ensure untested: when not refuted? and n_tests = 0, verdict = Inconclusive

    expect realizability_never_fails: when kind = Kind::Realizability, verdict != Fail
    expect cover_never_fails: when kind = Kind::Cover, verdict != Fail
}
```

A `Pass` from testing is weaker than one from the checks: no counterexample
was found among the tests. A `Fail` is not: `fren check` fails the same
check on the same spec, unless the solver gives no answer.
`eval::sound` states this:

```fren
pub comp sound {
    in by_testing: Verdict   -- the verdict of testing a check
    pub out checked: Verdict  -- the verdict of `fren check` for it

    ensure no_false_pass: when by_testing = Fail, checked != Pass
}
```

Results are reported as by `fren check` (see [Diagnostics](View.md)), with
a summary that counts them by verdict, and the number of tests:

```text
fren: 6 passed, 1 failed, 0 inconclusive, in 100 tests each
```

The exit status is `fren check`'s (`cli::exit`).

## Confirming models

When the solver answers `Sat`, it gives a model: a value for each
variable of the query, and an interpretation. `fren check` evaluates the
query's hypotheses and its goal in the model. The model *confirms* the
answer if every hypothesis is `true` and the goal `false`, and *refutes*
it if some hypothesis is `false` or the goal `true`. A part that the
evaluator cannot decide, such as the realizability goal `∃ o. R` when the
search finds no outputs, or a value it cannot read, leaves the answer
*undecided*.

The goal of a [definedness](Check.md#definedness) check is that an index
is in range wherever its guard holds. The evaluator finds the guard itself,
from the constraint, definition or binding that has the index, by the same
left-to-right reading, and pairs it with the solver's by the index's
position in the source. An index out of range in the guard has no value
that the evaluator knows, so it leaves the goal undecided unless the rest
decides it. The goals of [completeness](Check.md#completeness),
[disjointness](Check.md#disjointness) and
[reachability](Check.md#reachability) are found in the same way, from the
patterns and guards of a `match`'s arms or a table's conditions, and
paired with the solver's by the place where each is reported in the
source, and by its question: a `match`'s `match` or a table's `table` for
its completeness, the later row's condition for the disjointness of two
rows, and an arm's pattern or a row's condition or `_` for its
reachability. In the body of a function, the parameters are the variables. The
goals of the [precondition](Check.md#preconditions) check are found in
the same way, each at the applied function's name, as its precondition
at the application's arguments, which the evaluator evaluates as it does
the function's body, or under the model's interpretation of the functions
that the precondition applies. A function's preconditions, and a defined
function's [postconditions](Check.md#postconditions), are the hypotheses
and goals of the checks of its body, over its parameters.
`eval::confirm` gives the result:

```fren
pub enum Confirmation { Confirmed, Refuted, Undecided }

use self::Confirmation::{Confirmed, Refuted, Undecided}

pub comp confirm {
    in hyp_false?        -- some hypothesis is false in the model
    in goal_true?        -- the goal is true in the model
    in all_known?        -- the hypotheses and the goal all have values
    pub det out result: Confirmation

    ensure refuted: when hyp_false? or goal_true?, result = Refuted
    ensure confirmed: when not hyp_false? and not goal_true? and all_known?, result = Confirmed
    ensure undecided: when not hyp_false? and not goal_true? and not all_known?, result = Undecided
}
```

A refuted model is a bug in Fren's translation of the spec, or in the
solver. The check that asked the query is then inconclusive, and Fren
reports an internal error naming the hypothesis or goal that the model
gets wrong. `eval::confirmed_verdict` gives the verdict, from the verdict
the solver's answers give and the confirmation of the models that the
check used:

```fren
pub comp confirmed_verdict {
    in solver: Verdict       -- from the solver's answers
    in result: Confirmation  -- the least confirmed of the check's models
    pub det out verdict: Verdict

    ensure refuted: when result = Refuted, verdict = Inconclusive
    ensure kept: when result != Refuted, verdict = solver

    expect bad_models_never_pass: when result = Refuted, verdict != Pass
}

#fren_check
```

Only the `fren` command confirms models. On a spec whose models are
never refuted, it gives the verdicts that Lean does (`cli::agreement`).
