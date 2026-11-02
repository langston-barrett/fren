# Evaluation and testing

```
fren eval --proc PATH [--set VAR=VALUE]... [--seed N] [-A|-W|-D|-F LINT]... FILE...
fren quickcheck [--tests N] [--seed N] [-A|-W|-D|-F LINT]... FILE...
```

The [checks](Check.md) ask a solver about every behaviour of a procedure
at once. Fren can also evaluate a spec on one behaviour at a time, without
the solver: `fren eval` evaluates the constraints of a procedure on a
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

A *behaviour* of a procedure is an
[interpretation](Lang/Procedures.md#interpretations), together with a value
for each of the procedure's variables: its inputs and outputs, and the
variables of its calls, including those that are hidden (see
[Calls](Lang/Calls.md#call-variables)). A behaviour of a
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
variable's [subset type](Lang/SubsetTypes.md) brings is a
constraint of its procedure, as for the solver: an input's among the
assumptions, an output's among the guarantees, and a call's input's
among the assumptions of the called procedure, which the call
check asks of the arguments. A value is of a type if it matches the
type's pattern, and so do all its fields, payloads and elements, at every
depth, and each `Nat` within it is at least 0. An uninterpreted function's
values are of its result type. In `fren eval`, such a constraint is shown
as `type x`, after the variable it is about. In the notation of
[Procedures](Lang/Procedures.md#meaning), a behaviour is *admissible* if
`A` and `I` hold in it, and it *meets* the procedure if `R` holds as well.
`eval::status` gives the status of a behaviour:

```fren
pub enum Status { Inadmissible, Violates, Meets }

use self::Status::{Inadmissible, Meets, Violates}

set_option fren.evidence "enumerated" in
pub proc status(
    assumes?,            -- every assumption holds
    insts?,              -- every call's constraint `I_w` holds
    guarantees?,        -- every guarantee holds
): (det status: Status) {
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

## Higher-order functions

The evaluator unfolds an application of a [higher-order
function](Lang/HigherOrder.md) as the solver's queries do: its body, with
each parameter standing for its argument, and each application of a
function parameter replaced by the closure's body, with the closure's
parameters standing for the application's arguments. A function's name
given for a function parameter is the closure that applies it. Before each
unfolding, the names that the body binds are renamed to names of their
own, and a closure's parameters have names of their own, so that neither
captures the other's, even where a body is unfolded within a copy of
itself, as in `map(o, |x| map(p, |y| x + y))`. A closure's preconditions are
then evaluated where it is applied, as the checks ask them. For the
function's own checks, each function parameter is an uninterpreted
function, whose values the interpretation gives.

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
  that the expression `e` of the conjunct `x in e` at `lo` has, as values
  of the bound name's type: where the conjunct reads a newtype's field
  `0`, as `m.0 in e` does (`lang::name_alone`), each member is the value
  whose field it is;
- for `Range`, the integers from the expression of the lower bound at
  `lo`, plus 1 if it is strict, up to that of the upper bound at `hi`,
  minus 1 if it is strict, where the bound name's type is one that a
  comparison bounds at all (`lang::range_domain`), and no domain where it
  is not: a `String`, an ordered record or an ordered enumeration has
  none, so a quantifier over one cannot be tested (`F0639`), while
  enumeration gives it its type's values up to the bound;
- for `FromZero`, those from 0 up to the upper bound's, for a bound name
  whose values are naturals (`lang::nat_floor`): a `Nat`, or a newtype
  over one.

A value that is not of the bound name's type is left out: a negative one
for a `Nat`, and one that does not satisfy the invariants of its subset type. The body is
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
procedure, global expectation or refinement, a quantifier without a domain
in what the test evaluates is an error (`F0639`), at the quantifier, and
the tests of what reads it are not run: its constraints, its definitions,
its calls' procedures, and the bodies of the functions and values of
the constants that those apply, read directly or through others. The
solver decides such a check, or a `trusted` claim stands for it. A domain
that has no value, or too many, in one behaviour only leaves that
behaviour without a value for the quantifier, as an index out of range
does, so the test that finds it reaches nothing.

[Enumeration](Check.md#quantifiers-up-to-the-bound) is not testing, and
`F0639` is not raised there: it gives a bound name without a domain its
type's values up to the bound, and the quantifier is true, false or
unknown over them.

## Fuel

Evaluation is total: it spends *fuel*, and a value that would need more
than it has is unknown. Fuel is counted in steps of the semantics, never
in steps of the evaluator, so that however the evaluator is optimized, the
same evaluations run out. With fuel `n`, evaluation reads each
[structural recursion](Lang/Recursion.md#meaning) `f` as its `n`th
approximation: the 0th has no point anywhere, and the `k + 1`th's point at
the arguments `l` is the outcome of `f`'s body at `l`, with `f`'s
applications read as the `k`th. So an application of `f` spends one unit,
for its body, and its arguments none. Checking that a value is of a
[subset type](Lang/SubsetTypes.md) spends one unit for each invariant that
it evaluates, likewise. Nothing else spends fuel: an expression's parts,
quantifiers, `match`es and the definitions read through
[`let` and `where`](Lang/Let.md) do not. Outcomes are monotone, so a
known outcome under an approximation is the recursion's own, and running
out only leaves a value unknown, which the test then neither refutes nor
reaches a check by (see below). Fren's evaluator has `2^20` units of fuel
(`evalFuel`), far more than any evaluation needs. It also bounds how deeply
it nests between two steps (`evalDepth`), only to be total, at a depth that
no spec reaches; that rests on source size and is not tested.

## Searching for behaviours

Both commands search for behaviours. The search chooses the variables in
order: the inputs, then the variables whose
[definitions](Lang/Procedures.md#definitions) mention only inputs and
such variables, computed from them, then each call's variables, the
call's inputs being its arguments' values, then the other outputs. It tries each variable's
candidates in a random order, and goes back when a constraint that can
already be evaluated is false (see [Backjumping](#backjumping)). An
assumption that reads such a variable is evaluated with its definition in
its place, so that it reads it computed, and, where the definition has
no value, decides the assumption as strong Kleene logic does. So is a
called procedure's assumption, with that procedure's definitions, on the
call's inputs. The
values that the constraints equate a variable with come first. The others,
its *pool*, are drawn once in each search, random parts included, and
shuffled again each time the search reaches the variable, in an order
drawn from the values chosen before it. A variable's candidates are:

- both `Bool`s, and each variant of an enumeration, with a payload built
  from the candidates of its types, to a bounded depth, taking a few of
  each variant's in turn where there are many;
- for an `Int`, small integers, the integer literals and constants of the
  procedure, its expectations included, and their neighbours, random integers, and the value of
  any expression that a constraint equates the variable with, such as `x
  + 1` in `y = x + 1`;
- for a `Nat`, those of an `Int` that are at least 0;
- for an abstract type `T`, `T#0` up to a random bound;
- for a `String`, `""`, `"a"` and `"b"`; the string literals and constants
  of the procedure, its expectations included, each also with `"a"` before
  and after it, and, for those of up to six characters, what remains after
  each of their first characters, such as the `:*` of `::*`, so that
  `s.contains?("..")` and `s.starts_with?("x")` have strings that satisfy
  them; a few random strings that match each pattern of a `matches?` in
  the procedure, each also followed by `"a"`; and the value of any
  expression that a constraint equates the variable with;
- for a `Set<T>`, the empty set, singletons of the candidates of `T`, a
  few random sets of two, three and four of them, and the value of any
  expression that a constraint equates the variable with;
- for a `Seq<T>`, the empty sequence, and sequences of one and two of the
  candidates of `T`; for each integer candidate from 3 to 4, such as the
  `3` of `q.len = 3`, a few random sequences of that length; and the value
  of any expression that a constraint equates the variable with. An index
  out of range has no value that the evaluator knows, since it is part of
  the interpretation;
- for a `Rel<A, B>`, the empty relation, single pairs of candidates of `A`
  and `B`, and, if `A` is `B`, a chain of two pairs, so that `closure` has
  something to close.

The interpretation is chosen at random: each function's value at each
argument is random, but the same wherever it is applied in the behaviour,
and at least 0 if its result is a `Nat`. Where the arguments meet the
function's [preconditions](Lang/Items.md#contracts), the value is the first
of a few random values that meets its postconditions; if none does, the
application has no value that the evaluator knows, as an index out of
range has none, since a value that does not meet them is no
interpretation of the spec. A [generic
function](Lang/GenericFunctions.md#uninterpreted-generic-functions)
without a body has a function of its own at each instance, the one that
the types of an application's arguments give it, with its result type at
that instance. Where they do not give each of its type arguments, as the
type expected of an application may instead, the application has no value
that the evaluator knows. So is the value of each type that
a [table](Lang/Expressions.md#tables) without a `_` row has where no row
holds, and a [`match`](Lang/Expressions.md#matches) where no arm is taken,
which the interpretation gives, as the solver's does: one value of
each type, the same for every such table and `match`.

The search may miss a behaviour that exists, since it tries only some
values, but every behaviour it reports is genuine: it is a behaviour of the
procedure, with the status that the evaluator gives it.

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
core](Lang/Decidability.md), so the procedure opts out:

```fren
set_option fren.lint.undecidable "allow" in
pub proc conflict(
    position: Int,              -- the variable's position among those the search chooses
    earlier: Int,               -- another variable's position
    equated?,                   -- an expression that the variable is equated with reads `earlier`
    rejections: Seq<Bool>,      -- for each candidate tried, whether what rejected it reads `earlier`
): (
    det member?,                -- `earlier` is in the variable's conflict set
) {
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
pub proc backjump(
    conflict: Seq<Bool>,     -- for each earlier variable, in order, whether it is in the conflict set
    k: Int,                  -- an earlier variable's position
): (
    det resumes?,            -- the search resumes at `k`
) {
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
pub proc backjumping(
    by_backtracking?,            -- backtracking over the same candidates finds a behaviour within the budget
    exhausted?,                  -- backtracking tries every candidate within the budget, and finds none
    backtracking_steps: Nat,     -- the candidates that backtracking tries
): (
    found?,                      -- the search finds a behaviour
    same?,                       -- it is the behaviour that backtracking finds
    steps: Nat,                  -- the candidates that the search tries
) {
    assume one_outcome: not (by_backtracking? and exhausted?)

    ensure finds: when by_backtracking?, found? and same? and steps <= backtracking_steps
    ensure fails: when exhausted?, not found? and steps <= backtracking_steps
}
```

## `fren eval`

`fren eval --proc PATH FILE...` evaluates a behaviour of the procedure
`PATH` of the spec in the files. `--set x=VALUE` gives the variable `x` a
value, as does `--set w.x=VALUE` for a variable of the call `w`.
`VALUE` is typed as an argument for `x` would be: a `Nat` is widened to an
`Int`, and an `Int`, such as `5 - 3`, is not accepted for a `Nat`. The
variables that are not set, and the interpretation, are chosen by
[searching](#searching-for-behaviours) for a behaviour that meets the
procedure, starting from `--seed` (default 0). If the search finds none,
the variables not set have no value, and nor does any constraint that
depends on them.

The command writes to standard output the value of each variable and of
each constraint (`true`, `false` or `unknown`), and the behaviour's
status. A value that is not of its variable's type, or a variable that
the procedure does not have, is an error in the arguments.
`eval::eval_exit` gives the exit status:

```fren
pub proc eval_exit(
    ran?,                -- the spec and the arguments have no errors
    complete?,           -- every variable has a value
    status: Status,
    expect_false?,       -- some expectation is false
): (det code: Int) {
    ensure not_run: unless ran?, code = 2
    ensure incomplete: when ran? and not complete?, code = 3
    ensure fails: when ran? and complete? and (status != Meets or expect_false?), code = 1
    ensure passes: when ran? and complete? and status = Meets and not expect_false?, code = 0

    expect zero_means_met: when code = 0, status = Meets and not expect_false?
}

use cli::exit_status

expect eval_exit_status(ran?, complete?, status: eval::Status, expect_false?) {
    use eval
    call concrete := eval_exit(ran?, complete?, status, expect_false?)
    refines concrete exit_status(ran?)
}
```

## `fren quickcheck`

`fren quickcheck FILE...` tests every procedure, global expectation and
[refinement](Lang/Refinement.md) of the spec on random behaviours: a
refinement as the procedure that checks it, for the checks that run on it. For each, it runs `--tests` tests (default
100), starting from `--seed` (default 0), so a run can be repeated. Each
test chooses a random interpretation and searches for an admissible input.
For each call in turn, it confirms the called procedure's assumptions on the
call's inputs, then searches for the call's behaviour. Last, it
searches for outputs that meet the procedure. A global expectation's
test searches for a behaviour that meets each binder's procedure.

Testing reports what it finds as the checks report it, at the same
positions (see [Check results](View.md#check-results)):

| Check | Testing reports |
|---|---|
| Expectations | a behaviour that meets the procedure, in which the expectation is false |
| Cover goals | a behaviour that meets the procedure, in which the goal holds: a witness, which passes it |
| Global expectations | as for a procedure: values of the parameters, with behaviours of the calls, in which an expectation is false; in the short form, none, since it has no variables |
| Call assumptions | an admissible input, with behaviours of the earlier calls, on which an assumption of the called procedure is false |
| Determinism | two behaviours on the same input, with different values of the `det` output |
| Realizability | an admissible input, with behaviours of the calls, for which the search found no outputs |

Vacuity and redundancy are not tested: they ask whether something can
hold at all, which a failed search does not refute. A [cover
goal](Check.md#cover-goals) asks that too, but a behaviour found shows
that it can hold, so testing passes a goal for which it finds a witness,
and never fails one. Nor are definedness,
completeness, disjointness and reachability (see [Checking by
testing](Check.md#checking-by-testing)).

A test *reaches* a check when it finds what the check is about, as in the
table: a behaviour that meets the procedure, for an expectation; an
admissible input with behaviours of the earlier calls, for a
call assumption; and so on. For an expectation, a global expectation
or a call assumption with a [trigger](Lang/Procedures.md#triggers),
the trigger must also hold: where it is false, the constraint holds by its
trigger alone, so the test says nothing about it. Since a random behaviour
seldom satisfies a narrow trigger, testing searches for one that does:

- for an expectation with a trigger, each test whose behaviour does not
  reach it searches again, from a new input, for a behaviour that meets the
  procedure and in which the trigger holds;
- a global expectation is tested as a procedure is, its parameters as
  inputs;
- for a cover goal without a witness yet, each test searches, from a new
  input, for a behaviour that meets the procedure and in which the goal
  holds. A cover goal is reached by a test that finds a witness: it is
  `reaches` with the goal as its trigger.

Testing also searches for counterexamples directly: for an expectation or
a global expectation not yet refuted, each test that finds what the
expectation is about (a behaviour that meets the procedure, or behaviours
of the binders in which the body's trigger holds, if it has one) also
searches for one in which it is false. Backtracking then tries combinations of candidates that random
behaviours seldom reach, such as a lexeme and the input after it that
together refute a rule about both. A behaviour found is a counterexample;
none found says nothing.

So a trigger that no search satisfies costs one more search in each test,
for each expectation that has it, and each expectation not yet refuted
costs one more, the direct search for a counterexample. A call
assumption's trigger gets no such search: it is about a call's
inputs, which its arguments give.

One more search tells apart the warnings below, after the tests, so that
it changes no other result: each procedure's tests have a random stream
of their own. For a global expectation, where some test found behaviours
of its binders but the trigger held in none of them, it searches for
behaviours of the binders, at most once for each test that `--tests`
asks for, with a test's budget, and stops at the first one in which the
trigger has no value.

A test reaches a check only where the check has a value in what the test
found, too, and so does its trigger, if it has one: a trigger without a
value does not hold. Where the check has none, as where an index is out of range, a
function has no value that the evaluator knows, no case of a table or
`match` is taken, or evaluation runs out of [fuel](#fuel), the test refutes
nothing, and it says nothing either: counting it would let an expectation
pass by testing that no test ever evaluated. A check that has no value in
any test is inconclusive, with the warning that `eval::unreached` gives.
`eval::reaches` states when a test reaches a check:

```fren
set_option fren.evidence "enumerated" in
pub proc reaches(
    found?,                  -- the test found what the check is about
    has_trigger?,
    trigger: Option<Bool>,   -- the trigger's value in what the test found, `None` if it has none
    value: Option<Bool>,     -- the check's value in what the test found, `None` if it has none
): (det reached?, det counted?, det trigger_unknown?) {
    ensure rule: reached? iff (found? and (not has_trigger? or trigger = Option::Some(true)) and value != Option::None)
    -- The test counts toward `unreached`'s `triggered`, and toward its
    -- `unknown` where the trigger has no value.
    ensure counts: counted? iff (found? and (not has_trigger? or trigger != Option::Some(false)))
    ensure unknown: trigger_unknown? iff (found? and has_trigger? and trigger = Option::None)

    expect false_trigger_never: when has_trigger? and trigger = Option::Some(false), not reached?
    expect valueless_trigger_never: when has_trigger? and trigger = Option::None, not reached?
    expect valueless_never: when value = Option::None, not reached?
    expect reached_counted: when reached?, counted? and not trigger_unknown?
    expect unknown_counted: when trigger_unknown?, counted?
}
```

A counterexample from testing is genuine, so it fails the check. But
the search can miss outputs, so an input for which none were found
suggests that the procedure is not realizable, without showing it. That
gives a warning, `F0609`, and an inconclusive result, unless the search
saw every output for that input. It does where each output without a
definition is of a type with finitely many values, all of which the
search tries: `Bool`, an abstract type, of the interpretation's number of
values, and an enumeration whose variants have no fields; where there are
at most 4096 assignments of those outputs; and where, in each of those,
with the defined outputs given by their definitions, every definition has
a value and some constraint of the procedure is `false`. Then no output
exists for that input, as for enumeration where it sees every output
(`check::enumerated_verdict`), so the input is a genuine counterexample,
and fails realizability, with the constraints that are `false` as its
core. `eval::outputs_seen` states when the search saw every output:

```fren
-- What one assignment of the outputs makes of the constraints: some is
-- `false`, with every definition's value; none is, and all have values;
-- or something it needs has no value.
pub enum Assigned { Ruled, Satisfied, Undefined }

set_option fren.lint.undecidable "allow" in
pub proc outputs_seen(
    sizes: Seq<Option<Int>>,     -- each output without a definition: its number of values, where the search tries all
    count: Nat,                  -- the assignments of those outputs: the product of their numbers of values
    assignments: Seq<Assigned>,  -- what each assignment makes of the constraints, if there are at most 4096
): (det seen?) {
    ensure rule: seen? iff ((forall (s: Option<Int>), when s in sizes, s != Option::None) and count <= 4096 and assignments.len = count
        and (forall (a: Assigned), when a in assignments, a = Assigned::Ruled))

    expect unbounded_unseen: when sizes != [] and sizes[0] = Option::None, not seen?
    expect satisfied_unseen: when assignments != [] and assignments[0] = Assigned::Satisfied, not seen?
    expect undefined_unseen: when assignments != [] and assignments[0] = Assigned::Undefined, not seen?
}
```

`exhausted?` below is `seen?`, for the input that the search found no
outputs for. A check that no test reached is inconclusive, and
`eval::unreached` says why, from four counts of the tests: those that
found what the check is about, those of them in which its trigger, if it
has one, was not false, that is, held or had no value (`counted?`), those
of these in which the trigger had no value (`trigger_unknown?`), and
those in which the trigger held and the check had a value, which are the
tests that reached it (`reached?`). Where none found what it is about,
because no admissible behaviour was found, the procedure has the warning
`F0610`, at the procedure. Where some did, but the trigger was false in
all of them, the check has the warning `F0612`, at its trigger. Where the
check has no trigger, or its trigger was not false in some of them, but
in none did both have a value, it has the warning `F0617`: at the check,
where in some of them the trigger held and the check had no value, and
else at its trigger, which had no value in all of them in which it was
not false:

```fren
-- Why testing reached a check, or did not.
pub enum Unreached { Reached, Untested, Untriggered, Valueless, TriggerValueless }

pub proc unreached(
    found: Nat,          -- the tests that found what the check is about
    triggered: Nat,      -- those of them in which its trigger, if it has one, was not false
    unknown: Nat,        -- those of these in which the trigger had no value
    decided: Nat,        -- those of them in which the trigger held and the check had a value: the tests that reached it
): (det why: Unreached) {
    assume counted: decided + unknown <= triggered <= found

    ensure reached: when decided > 0, why = Unreached::Reached
    ensure untested: when found = 0, why = Unreached::Untested
    ensure untriggered: when found > 0 and triggered = 0, why = Unreached::Untriggered
    -- In some test the trigger held, but the check had no value.
    ensure valueless: when unknown < triggered and decided = 0, why = Unreached::Valueless
    -- The trigger had no value wherever it was not false.
    ensure trigger_valueless: when triggered > 0 and unknown = triggered and decided = 0,
        why = Unreached::TriggerValueless

    expect warned_only_unreached: when why != Unreached::Reached, decided = 0
}
```

Beside the procedure's `F0610`, which already says that no admissible
behaviour was found, a check's `F0612` is not given, and an
expectation's `F0617` is not either. A call assumption's `F0617` is,
where the assumption as a whole, its trigger included, had no value in
any test that found the call's inputs: an assumption without a value
admits nothing, so its `F0617` says why the procedure has `F0610`. One whose
trigger has no value but which holds, as `when q[7] > 0, q.len >= 0`
does, admits everything, so it explains nothing, and is not given. A
call's inputs may be found where no behaviour is.
`eval::unreached_warning` gives the warning shown at a check, from the
counts of `unreached`:

```fren
-- The warning shown at a check that no test reached: none, `F0612`, or
-- `F0617` at the check or at its trigger.
pub enum UnreachedWarning { Silent, Untriggered, Valueless, TriggerValueless }

pub proc unreached_warning(
    found: Nat,              -- as for `unreached`
    triggered: Nat,
    unknown: Nat,
    decided: Nat,
    valued: Nat,             -- the tests that found what it is about in which the check as a whole, its trigger included, had a value
    untested?,               -- the procedure has `F0610`
    call_assumption?,        -- the check is a call assumption
): (det shown: UnreachedWarning) {
    assume counted: decided + unknown <= triggered <= found
    assume valued_counted: valued <= found

    call u := unreached(found, triggered, unknown, decided)

    ensure reached_silent: when u.why is Unreached::Reached | Unreached::Untested, shown = UnreachedWarning::Silent
    ensure untriggered: when not untested? and u.why = Unreached::Untriggered, shown = UnreachedWarning::Untriggered
    ensure valueless: when (not untested? or (call_assumption? and valued = 0)) and u.why = Unreached::Valueless,
        shown = UnreachedWarning::Valueless
    ensure trigger_valueless: when (not untested? or (call_assumption? and valued = 0)) and u.why = Unreached::TriggerValueless,
        shown = UnreachedWarning::TriggerValueless
    ensure beside_untested: when untested? and not (call_assumption? and valued = 0 and u.why is Unreached::Valueless | Unreached::TriggerValueless),
        shown = UnreachedWarning::Silent

    -- Beside `F0610`, only the `F0617` of a call assumption that had no
    -- value as a whole in any test is shown, which explains it.
    expect only_call_assumptions_beside_untested: when untested? and shown != UnreachedWarning::Silent,
        call_assumption? and valued = 0 and shown is UnreachedWarning::Valueless | UnreachedWarning::TriggerValueless
    -- `F0617` blames the trigger only where it had no value.
    expect trigger_blamed_only_unknown: when shown = UnreachedWarning::TriggerValueless, unknown > 0
    expect warns_only_unreached: when decided > 0, shown = UnreachedWarning::Silent
}
```

A cover goal for which no test found a witness, though some found a
behaviour that meets the procedure, is inconclusive with the warning
`F0616`, at the goal, likewise. `eval::test_verdict` gives the verdict of testing one
check, from whether some test refuted it and how many tests reached it:

```fren
pub proc test_verdict(
    kind: Kind,
    refuted?,            -- some test is a counterexample, or an input without outputs
    n_tests: Nat,        -- the tests that reached the check (`reaches`)
    exhausted?,          -- for realizability: the search saw every output of such an input
): (det verdict: Verdict) {
    assume testable: not kind is Kind::Vacuity | Kind::Redundancy
    -- A cover goal is reached by its witnesses, which refute nothing.
    assume witnesses: when kind = Kind::Cover, not refuted?

    ensure definite: when refuted? and (kind != Kind::Realizability or exhausted?), verdict = Fail
    ensure not_found: when refuted? and kind = Kind::Realizability and not exhausted?, verdict = Inconclusive
    ensure passes: when not refuted? and n_tests > 0, verdict = Pass
    ensure untested: when not refuted? and n_tests = 0, verdict = Inconclusive

    expect realizability_fails_exhausted: when kind = Kind::Realizability and not exhausted?, verdict != Fail
    expect cover_never_fails: when kind = Kind::Cover, verdict != Fail
}
```

Testing that runs a check fails it only where the
[matrix](Methods.md#the-matrix) has it refute the check: those whose pass
is a proof, realizability among them. Its pass of such a check, where it
finds no counterexample, is the one that `"random"` chosen alone reports,
with the caveat `Random`:

```fren
use check::{Cell, ProofMethod, method_cell, testable?}

expect random_within_matrix(kind: Kind, refuted?, n_tests: Nat, exhausted?) {
    assume run: testable?(kind)
    assume witnesses: when (kind) = Kind::Cover, not (refuted?)
    call t := test_verdict(kind, refuted?, n_tests, exhausted?)
    call cell := method_cell(kind, ProofMethod::Random)
    expect fails_where_refutes: when (t.verdict) = Fail, (cell.cell) = Cell::Refutes
}
```

A `Pass` from testing is weaker than one from the checks: no counterexample
was found among the tests. A `Fail` is not: `fren check` fails the same
check on the same spec, unless the solver gives no answer.
`eval::sound` states this:

```fren
set_option fren.evidence "enumerated" in
pub proc sound(
    by_testing: Verdict,     -- the verdict of testing a check
): (
    checked: Verdict,         -- the verdict of `fren check` for it
) {
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
from the constraint, definition or argument that has the index, by the same
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

set_option fren.evidence "enumerated" in
pub proc confirm(
    hyp_false?,          -- some hypothesis is false in the model
    goal_true?,          -- the goal is true in the model
    all_known?,          -- the hypotheses and the goal all have values
): (det result: Confirmation) {
    ensure refuted: when hyp_false? or goal_true?, result = Refuted
    ensure confirmed: when not hyp_false? and not goal_true? and all_known?, result = Confirmed
    ensure undecided: when not hyp_false? and not goal_true? and not all_known?, result = Undecided
}
```

The goal of a [realizability](Check.md#realizability) check, `∃ o. R`, is
not read from the model, which gives no outputs for it: the evaluator
searches for them, and the goal is `true` where it finds outputs that are
of their declared types, subset types included, and meet the guarantees in
the model; otherwise it is unknown, since a search that finds none decides
nothing. So an output that the guarantees allow but its type does not
refutes nothing (`test/ui/checks/realizable_subset_outputs.fren`).
`eval::outputs_confirm` computes the goal so, over the values that an
output may take, and confirms the model with it:

```fren
-- A value of the procedure's outputs, all of them together.
pub type OutputValue

pub proc outputs_confirm(
    hyp_false?,                  -- some hypothesis is false in the model
    hyps_known?,                 -- the hypotheses all have values
    declared: Set<OutputValue>,  -- the values of the outputs' declared types, subset types included
    meeting: Set<OutputValue>,   -- those values, or others, that meet the guarantees in the model
    tried: Set<OutputValue>,     -- the values that the evaluator's search tries
): (det goal_true?, det result: Confirmation) {
    out goal_true? := tried inter declared inter meeting != {}
    call c := confirm(hyp_false?, goal_true?, hyps_known? and goal_true?)
    out result := c.result

    expect outside_types: when tried inter declared = {}, result != Refuted or hyp_false?
    expect found_refutes: when tried inter declared inter meeting != {}, result = Refuted
    expect none_found_decides_nothing: when not hyp_false? and tried inter declared inter meeting = {},
        result = Undecided
}
```

A refuted model is a bug in Fren's translation of the spec, or in the
solver. The check that asked the query is then inconclusive, and Fren
reports an internal error naming the hypothesis or goal that the model
gets wrong. `eval::confirmed_verdict` gives the verdict, from the verdict
the solver's answers give and the confirmation of the models that the
check used:

```fren
set_option fren.evidence "enumerated" in
pub proc confirmed_verdict(
    solver: Verdict,         -- from the solver's answers
    result: Confirmation,    -- the least confirmed of the check's models
): (det verdict: Verdict) {
    ensure refuted: when result = Refuted, verdict = Inconclusive
    ensure kept: when result != Refuted, verdict = solver

    expect bad_models_never_pass: when result = Refuted, verdict != Pass
}

#fren_check
```

Only the `fren` command confirms every model. Both front ends confirm
each model that they report, as a counterexample or a witness, at the
values that they show (see [Reading models](Models.md)). On a spec whose
models are never refuted, the `fren` command gives the verdicts that Lean
does (`cli::agreement`).
