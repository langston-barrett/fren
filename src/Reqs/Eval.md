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
of range, or a table or `match` where no row or arm is taken, or that has
an [unbounded quantifier](#quantifiers), is kept as its expression: in
each behaviour, it has the value that the interpretation gives the table
or `match`, none for the index, and the quantifier's where it is
mentioned, as [Quantifiers](#quantifiers) gives it; its indexes, tables
and `match`es are the constant's own, which the checks ask about at the constant, not
where it is mentioned. A constant whose value cannot be computed for any
other reason is an internal error. The evaluator computes it from the
spec itself, not from the formulas given to the solver, so it is an
independent statement of what a spec means. A name of a
[`let` or `where`](Lang/Let.md) is read as its definition, so it is not
part of a behaviour, and counterexamples show variables only. What a
variable's [pattern type](Lang/Types.md#pattern-types) brings is a
constraint of its component, as for the solver: an input's among the
assumptions, an output's among the guarantees, and an instance's input's
among the assumptions of the instantiated component, which the instance
check asks of the bindings. A value is of a type if it matches the
type's pattern, and so do all its fields, payloads and elements, at every
depth, and each `Nat` within it is at least 0. An uninterpreted function's
values are of its result type. In `fren eval`, such a constraint is shown
as `type x`, after the variable it is about. In the notation of
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

## Quantifiers

The evaluator evaluates a [quantifier](Lang/Quantifiers.md) over listed
types by its expansion: the conjunction or disjunction of its instances,
decided as soon as one instance decides it. It evaluates an [unbounded
quantifier](Lang/Quantifiers.md#unbounded-quantifiers) by enumerating the
values of each bound name in turn, in the order that they are written:
those of its type, for a bound name of a listed type, and those of its
[domain](Lang/Quantifiers.md#guards), for any other, evaluated with the
values of the bound names before it:

- for `Members`, the members of the set, or the elements of the sequence,
  that the expression `e` of the conjunct `x in e` at `lo` has;
- for `Range`, the integers from the expression of the lower bound at
  `lo`, plus 1 if it is strict, up to that of the upper bound at `hi`,
  minus 1 if it is strict;
- for `FromZero`, those from 0 up to the upper bound's.

A value that is not of the bound name's type is left out: a negative one
for a `Nat`, and one that its pattern type does not match. The body is
evaluated at each combination of the values, and the quantifier is the
conjunction of those values for a `forall`, and their disjunction for an
`exists`, decided as soon as one decides it. That is its value: at any
value outside the domain, a conjunct of the guard is false, so the body
of a `forall` is true there, and that of an `exists` false, which changes
neither. So `forall (i: Int), when 0 <= i < q.len, q[i] > 0` is evaluated
at each position of `q`, and `exists (x: Name), x in s and p?(x)` at each
member of `s`.

A quantifier has no value that the evaluator knows, as an index out of
range has none, where a bound name of a type that is not listed has no
domain, where the expression of a domain has none, and where a range has
more than `MAX_ENUMERATED` values:

```fren
pub const MAX_ENUMERATED: Int := 1024
```

Beyond `MAX_ENUMERATED`, then, a test gives no evidence about what reads
the quantifier: a behaviour where it has no value is not one that the
search can find, so the checks it reaches are reported as for any other
behaviour not found, inconclusive with `F0610` or `F0612`, and a model
that the solver gives is left undecided (see [Confirming
models](#confirming-models)). `fren eval` then shows the constraints that
read it as `unknown`. A check
that needs it cannot be tested: when `fren check` [tests a
check](Check.md#checking-by-testing), and when `fren quickcheck` tests a
component, global expectation or refinement, a quantifier without a domain
in what the test evaluates is an error (`F0639`), at the quantifier, and
the tests of what reads it are not run: its constraints, its definitions,
its instances' components, and the bodies of the functions and values of
the constants that those apply, read directly or through others. The
solver decides such a check, or a `trusted` claim stands for it. A domain
that has no value, or too many, in one behaviour only leaves that
behaviour without a value for the quantifier, as an index out of range
does, so the test that finds it reaches nothing.

## Searching for behaviours

Both commands search for behaviours. The search chooses the variables in
order: the inputs, then the [defined
outputs](Lang/Components.md#defined-outputs) whose definitions mention
only inputs and such outputs, computed from them, then each instance's
variables, the instance's inputs being its bindings' values, then the
other outputs. It tries each variable's
candidates in a random order, and goes back when a constraint that can
already be evaluated is false (see [Backjumping](#backjumping)). The
values that the constraints equate a variable with come first. The others,
its *pool*, are drawn once in each search, random parts included, and
shuffled again each time the search reaches the variable, in an order
drawn from the values chosen before it. A variable's candidates are:

- both `Bool`s, and each variant of an enumeration, with a payload built
  from the candidates of its types, to a bounded depth, taking a few of
  each variant's in turn where there are many;
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
- for a `Set(T)`, the empty set, singletons of the candidates of `T`, a
  few random sets of two, three and four of them, and the value of any
  expression that a constraint equates the variable with;
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

### Backjumping

A search has a *budget*: it tries at most 4000 candidates in all, then
gives up. A constraint that is already false before the search chooses
anything stays false, so the search then gives up at once. Otherwise, when
a variable has no candidate left, the search goes back to the last
variable that its *conflict set* names, not to the one before it. The
conflict set holds the earlier variables that the failure of every
candidate depends on. A variable `j` before the variable that has run out
is in it if:

- an expression that the variable is equated with reads `j`, since its
  candidates come from those expressions; or
- for some candidate, what rejected it reads `j`. That is the constraint
  that the candidate made false, the first that the search found. If the
  search found no constraint false but went on to the next variable, it is
  the conflict set that the search came back with, from there. At the last
  variable, it is the first constraint that is not true once every
  variable has a value.

`eval::conflict` states this for one earlier variable. Membership in a
sequence of unknown length is outside the [decidable
core](Lang/Decidability.md), so the component opts out:

```fren
set_option fren.lint.undecidable "allow" in
pub comp conflict {
    in position: Int            -- the variable's position among those the search chooses
    in earlier: Int             -- another variable's position
    in equated?                 -- an expression that the variable is equated with reads `earlier`
    in rejections: Seq(Bool)    -- for each candidate tried, whether what rejected it reads `earlier`
    pub det out member?         -- `earlier` is in the variable's conflict set

    ensure rule: member? iff (0 <= earlier < position and (equated? or true in rejections))

    expect earlier_only: when earlier >= position, not member?
    expect unread: when not equated? and not (true in rejections), not member?
}
```

The search resumes at the last variable of the conflict set, with its
next candidate, and adds the rest of the conflict set to that variable's
own. It goes back past the variables after that one without trying their
other candidates, since no value of theirs changes what rejected each
candidate. If the conflict set is empty, the search fails. `eval::backjump`
states where it resumes:

```fren
set_option fren.lint.undecidable "allow" in
pub comp backjump {
    in conflict: Seq(Bool)   -- for each earlier variable, in order, whether it is in the conflict set
    in k: Int                -- an earlier variable's position
    pub det out resumes?     -- the search resumes at `k`

    ensure rule: resumes? iff (0 <= k < conflict.len and conflict[k] and not (true in conflict.slice(k + 1, conflict.len)))

    expect members_only: when resumes?, 0 <= k and conflict[k]
    expect empty_fails: when not (true in conflict), not resumes?
}
```

So a search tries the candidates that going back one variable at a time,
*backtracking*, would try over the same candidates, in the same order, but
for those of the variables it goes back past. None of those leads to a
behaviour, so it finds what backtracking finds. Both draw the same random
numbers, so the tests after it are the same too. It may find more, since
it reaches candidates that backtracking would have run out of budget
before. `eval::backjumping` states this:

```fren
pub comp backjumping {
    in by_backtracking?          -- backtracking over the same candidates finds a behaviour within the budget
    in exhausted?                -- backtracking tries every candidate within the budget, and finds none
    in backtracking_steps: Nat   -- the candidates that backtracking tries
    pub out found?               -- the search finds a behaviour
    pub out same?                -- it is the behaviour that backtracking finds
    pub out steps: Nat           -- the candidates that the search tries

    assume one_outcome: not (by_backtracking? and exhausted?)

    ensure finds: when by_backtracking?, found? and same? and steps <= backtracking_steps
    ensure fails: when exhausted?, not found? and steps <= backtracking_steps
}
```

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

    assume testable: not kind is Kind::Vacuity | Kind::Redundancy
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
