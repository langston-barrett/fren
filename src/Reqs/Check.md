# Checks

Fren checks each component seven ways:

| Check | Reported as | Confirms |
|---|---|---|
| [Realizability](#realizability) | `realizable` | some system can meet the guarantees, for every admissible input |
| [Expectations](#expectations) | `expect` | each expectation follows from the assumptions and guarantees |
| [Cover goals](#cover-goals) | `cover` | some behaviour that meets the assumptions and guarantees satisfies each cover goal |
| [Instance assumptions](#instance-assumptions) | `instance` | each instance's bindings satisfy the instantiated component's assumptions |
| [Vacuity](#vacuity) | `vacuity` | the trigger of each guarantee and expectation can hold |
| [Redundancy](#redundancy) | `redundancy` | no assumption or guarantee follows from the others |
| [Determinism](#determinism) | `determinism` | each `det out` is determined by the inputs |

and checks how its constraints are written six more ways, wherever they
have an index, a [table](Lang/Expressions.md#tables), a
[`match`](Lang/Expressions.md#matches) with guards, an application of a
function with a [contract](Lang/Items.md#contracts), or a value given
where a [pattern type](Lang/Types.md#pattern-types) is declared:

| Check | Confirms |
|---|---|
| [Definedness](#definedness) | each index is in range where it is evaluated |
| [Pattern types](#pattern-types) | each value given where a pattern type is declared matches its pattern |
| [Completeness](#completeness) | some row of each table without a `_` row holds, and some arm of each `match` that needs its guards to be exhaustive is taken, where it is evaluated |
| [Disjointness](#disjointness) | no two rows of a table, other than `_`, hold at once where it is evaluated |
| [Preconditions](#preconditions) | each application of a function meets the function's preconditions where it is evaluated |
| [Reachability](#reachability) | each arm of a `match` that has a guard or follows one, and each row of a table, can be taken where it is evaluated |

A [global expectation](Lang/Global.md) is checked two of the first six
ways: the [expectation check](#global-expectations) confirms that it holds,
and the [vacuity check](#vacuity) that its trigger can hold. The body of a
[defined function](Lang/Items.md#defined-functions), the value of a
[constant](Lang/Items.md#constants), and the clauses of a function's
[contract](Lang/Items.md#contracts) are checked for completeness,
disjointness, reachability and preconditions too, a defined function's
[postconditions](#postconditions) are checked to hold, and the values in a
body or a value given where pattern types are declared, including the body
or value itself, are checked for their patterns.

The formulas below use the notation of [Components](Lang/Components.md#meaning):
`A` is the conjunction of the component's assumptions, `R` of its
guarantees, and `I` of its instances, over the inputs `i`, the instances'
variables `y` and the outputs `o`.
`D` is the equations `d = e` of the component's [defined
outputs](Lang/Components.md#defined-outputs), and `o` excludes them.
`N` is the constraints that [natural
numbers](Lang/Components.md#natural-numbers), [pattern
types](Lang/Components.md#pattern-types) and the
[postconditions](Lang/Items.md#contracts) of uninterpreted functions
bring: `N(i, y)` that each `Nat` input and instance variable, and each
application of an uninterpreted function whose result is a `Nat` that the
query's own hypotheses or goal mention, is at least 0, and that each such
application of an uninterpreted function with postconditions meets each
of them if its arguments meet the function's preconditions; and `N(o)`
that each `Nat` output is at least 0; and likewise that each variable and
application whose type is a pattern type, or has one within its fields,
payloads or elements, matches it, and that each payload of a recursive
enumeration that the query reads matches its pattern type, if it has one.
Each variable's constraints come in the order of the variables, after its
`Nat`'s, and each application's or payload's in the order in which the
query mentions them, one application's as one fact each: its `Nat`'s, its
type's, then its postconditions'. So a query's facts about applications depend only on its
formulas: an instance's query has none about its component's
expectations, which are not among them. Every query has both among its hypotheses,
though the formulas below leave them implicit, and realizability also
puts `N(o)` under its `∃`, with the guarantees. Like `D`, they are never
candidates for redundancy, nor reported in a minimal set.

```fren
pub mod check
```

## Interpretations

A spec's [abstract types](Lang/Types.md#abstract-types) and
[uninterpreted functions](Lang/Items.md#uninterpreted-functions) are given
to the solver as sorts and uninterpreted functions. A [defined
function](Lang/Items.md#defined-functions) is given with its body, so the
solver knows its values. So the solver proves a goal from hypotheses when
the goal holds wherever the hypotheses do, under every
[interpretation](Lang/Components.md#interpretations), and a model gives an
interpretation as well as values for the variables. Hence:

- Realizability, expectations, instance assumptions and determinism pass
  only if they hold under every interpretation.
- A trigger is not vacuous, and a constraint not redundant, if that is so
  under some interpretation. Likewise, the assumptions are contradictory
  only if they are under every interpretation.

The formulas below hold for each interpretation, which they leave
implicit.

## Verdicts

Each check asks an SMT solver to prove a goal from hypotheses. The solver
either proves it (`Unsat`, since the negated goal is unsatisfiable), finds a
model of the hypotheses in which the goal is false (`Sat`), or gives no
answer (`Unknown`). A timeout, a crash, an unparseable response, and a goal
that cannot be translated for the solver are all `Unknown`. The time limit
for each query is set by the `fren.timeout` option in Lean, or `--timeout`
for the `fren` command; the default is 10 seconds. A limit on the solver's
work, which unlike a time limit does not depend on the machine's load, is
set by `fren.resourceLimit` or `--resource-limit`; by default there is
none (see [Limits](Cli.md#limits)).

From the solver's outcomes, each check reaches a verdict: `Pass`, `Fail` or
`Inconclusive`. An `Unknown` outcome never leads to `Pass`. Results are
trusted from the solver: no Lean proofs of them are produced.

```fren
pub enum Outcome { Sat, Unsat, Unknown }

pub enum Verdict { Pass, Fail, Inconclusive }

pub enum Kind {
    Realizability,
    Expectation,
    Cover,
    InstanceAssumption,
    Vacuity,
    Redundancy,
    Determinism,
    Definedness,
    Completeness,
    Disjointness,
    Precondition,
    Postcondition,
    Reachability,
}

use self::Outcome::{Sat, Unknown, Unsat}
use self::Verdict::{Fail, Inconclusive, Pass}
```

Every check but realizability reaches its verdict from one outcome, in
one of two ways. A check that asks the solver to *prove* something passes
when it is proved, and fails on a model, a counterexample; a check that
asks whether something *can hold* passes on a model, a witness, and fails
when its negation is proved. Either way, `Unknown` is inconclusive and
nothing else is. Both kinds ask the solver for a proof; they differ in
what a proof means. An expectation's proof is of the expectation, so it
passes; vacuity proves that the trigger cannot hold, and redundancy that
the constraint follows from the others, so a proof fails them, and a model,
in which the trigger holds or the constraint fails while the others hold,
passes them. `check::proved` and `check::satisfiable` state the two,
and each check below [refines](Lang/Refinement.md) one of them (see
[Verdict families](#verdict-families)):

```fren
pub comp proved {
    in q: Outcome          -- can the goal be proved?
    pub det out verdict: Verdict

    ensure proof: verdict = Pass iff q = Unsat
    ensure counterexample: verdict = Fail iff q = Sat

    expect conservative: when q = Unknown, verdict = Inconclusive
}

pub comp satisfiable {
    in q: Outcome          -- can the negation of the goal be proved?
    pub det out verdict: Verdict

    ensure witness: verdict = Pass iff q = Sat
    ensure refuted: verdict = Fail iff q = Unsat

    expect conservative: when q = Unknown, verdict = Inconclusive
}
```

`check::applies` gives which checks run on an item. A global expectation
constrains nothing, so there is nothing to realize, determine or find
redundant, and its binders' inputs have no obligations. The body of a
function, its contract, or the value of a constant is not a constraint
either: only its tables, its `match`es with guards, the applications in
it, and its values given where pattern types are declared are checked, and
the function's postconditions. The [pattern-type check](#pattern-types) is
part of definedness: its results are definedness results, and it runs
where definedness does, though in a body or a value, definedness asks
nothing of its indexes. A component has no postconditions, so their check
has no results there. The contract of an uninterpreted function with
postconditions is checked for [realizability](#realizability) too, as a
component whose inputs are the function's parameters, whose one `det out`
is its value, and whose assumptions and guarantees are its preconditions
and postconditions (see [Contracts](#contracts-of-uninterpreted-functions)):

```fren
pub enum CheckedItem { Component, GlobalExpectation, Body, Contract }

pub comp applies {
    use self::CheckedItem::{Body, Component, Contract, GlobalExpectation}
    use self::Kind::{
        Completeness,
        Definedness,
        Determinism,
        Disjointness,
        Expectation,
        Postcondition,
        Precondition,
        Reachability,
        Realizability,
        Vacuity,
    }
    in item: CheckedItem
    in kind: Kind
    pub det out runs?

    ensure rule: runs? iff match item {
        Component => true,
        GlobalExpectation => kind in {Expectation, Vacuity, Definedness, Completeness, Disjointness, Precondition, Reachability},
        Body => kind in {Definedness, Completeness, Disjointness, Precondition, Postcondition, Reachability},
        Contract => kind in {Realizability, Completeness, Disjointness, Precondition, Reachability},
    }

    expect claims_only: when item in {GlobalExpectation, Body} and runs?, not kind in {Realizability, Determinism}
    expect determined: when item != Component, kind != Determinism or not runs?
}
```

## Realizability

A component is realizable if some system can respond to every admissible
input, whatever its instances do:

  ∀ i y. A(i) ∧ I(i, y) ⇒ ∃ o. R(i, y, o)

with each defined output replaced by its definition (see
[Definitions](#definitions)), and `N(o)` a conjunct of `R`, so that the
outputs that `∃` ranges over are `Nat`s where their types say so.

Fren asks two queries:

- **Assumptions.** Can `False` be proved from `A`? If so, the assumptions
  are contradictory, so the formula above holds vacuously, and the check
  fails rather than passing. Fren reports a minimal set of contradictory
  assumptions.
- **Counterexample.** Can `∃ o. R(i, y, o)` be proved from `A` and `I`, with
  the inputs and instance variables free? A model is an input, together
  with a behaviour of the instances, that no system could answer. Fren
  reports it, with a minimal set of guarantees that conflict on it.

`check::realizability` gives the verdict and what is reported, from the
outcomes of the two queries (`assume_q` and `cex_q`). Its table's rows
cover the nine pairs of outcomes, each exactly once, which the
[completeness](#completeness) and [disjointness](#disjointness) checks
confirm:

```fren
pub comp realizability {
    in assume_q: Outcome   -- can `False` be proved from A?
    in cex_q: Outcome      -- can `exists outputs, R` be proved from A and I?
    pub det out verdict: Verdict
    pub det out reports_cex?   -- report the input and the conflicting guarantees
    pub det out reports_vacuous?  -- report that the assumptions are contradictory

    ensure verdict_rule: verdict = table {
        | assume_q = Unsat => Fail,
        | assume_q != Unsat and cex_q = Sat => Fail,
        | assume_q = Sat and cex_q = Unsat => Pass,
        | assume_q != Unsat and cex_q = Unknown => Inconclusive,
        | assume_q = Unknown and cex_q = Unsat => Inconclusive,
    }
    ensure report_cex: reports_cex? iff (assume_q != Unsat and cex_q = Sat)
    ensure report_vacuous: reports_vacuous? iff assume_q = Unsat

    expect never_upgrades: when assume_q = Unknown or cex_q = Unknown, verdict != Pass
    expect fail_explains: when verdict = Fail, reports_cex? or reports_vacuous?
}
```

### Contracts of uninterpreted functions

An uninterpreted function's [postconditions](Lang/Items.md#contracts)
are assumed at each of its applications, so if they cannot hold together,
every check that applies the function holds vacuously. So its contract is
checked as a component is: the inputs are its parameters `x`, the one
output is its value `v`, `A` is its preconditions, and `R` its
postconditions, with `v` for each application of the function to its
parameters:

  ∀ x. A(x) ⇒ ∃ v. R(x, v)

The other functions that the clauses apply are free, as they are in any
check, so a postcondition that says nothing of the function's value, and
can be false, as `ensure c: n > 0` of `fn other(n: Int): Int`, fails. The
functions that a contract applies are declared before it, so each
function's contract is checked once all of theirs have been: an
interpretation of each in turn meets them all. The two queries are those
of a component, and so are the verdicts, but the failures are reported at
the function's name: contradictory preconditions (`F0632`), and arguments
for which no value meets the postconditions (`F0631`), with a note at each
postcondition of a minimal set that conflicts on them.

`check::contract_realizability` states the verdict, over a small domain:
two arguments and two values, where the preconditions hold at the
arguments `pres`, and the postconditions at the pairs `posts`. Where no
argument meets the preconditions, they contradict each other, and the
check fails. Its
implementation builds the contract's component as both front ends do,
and runs the realizability check on it, with a solver that decides by
trying every argument and value:

```fren
pub enum Argument { A0, A1 }
pub enum Value { V0, V1 }
pub struct Point { arg: Argument, value: Value }

pub comp contract_realizability {
    in pres: Set(Argument)   -- the arguments that meet the preconditions
    in posts: Set(Point)     -- the arguments and values that meet the postconditions
    pub det out verdict: Verdict
    pub det out reports_cex?       -- report the arguments and the conflicting postconditions
    pub det out reports_vacuous?   -- report that the preconditions are contradictory

    ensure rule: verdict = (if pres != {}
        and (forall (a: Argument), when a in pres, exists (v: Value), Point { arg := a, value := v } in posts)
        then Pass else Fail)
    ensure vacuous: reports_vacuous? iff pres = {}
    ensure cex: reports_cex? iff (pres != {} and verdict = Fail)

    expect unrealizable: when posts = {}, verdict = Fail
    expect contradictory_preconditions: when pres = {}, verdict = Fail
    expect everywhere: when pres != {} and (forall (a: Argument), exists (v: Value), Point { arg := a, value := v } in posts),
        verdict = Pass
}
```

It refines `check::realizability`, the check of a component, whose
queries' answers are those of the contract over this domain: the
preconditions are contradictory exactly when no argument meets them, and
the postconditions can be proved satisfiable exactly when every argument
that meets the preconditions has a value that meets the postconditions:

```fren
refine contract_realizes: contract_realizability refines realizability {
    assume_q := if pres = {} then Unsat else Sat,
    cex_q := if forall (a: Argument), when a in pres, exists (v: Value), Point { arg := a, value := v } in posts
        then Unsat else Sat,
}
```

### Query order

The counterexample query is asked only when the assumptions query does not
return `Unsat`; otherwise its outcome is taken to be `Unknown`.
`check::realizability_protocol` confirms that this gives the same verdict
and reports as always asking both. `always` is the check with the solver's
answer to `cex_q`, and `asked` the check as Fren runs it:

```fren
expect realizability_protocol: forall (asked always: realizability),
    when asked.assume_q = always.assume_q
    and asked.cex_q = (if always.assume_q = Unsat then Unknown else always.cex_q),
    asked.verdict = always.verdict
    and (asked.reports_cex? iff always.reports_cex?)
    and (asked.reports_vacuous? iff always.reports_vacuous?)
```

## Definitions

A defined output is not a constraint, and the checks never search for its
value. Realizability replaces each defined output by its definition, so
that the `∃` ranges over the other outputs only, whose types are bounded.
Every other check adds `D` to its hypotheses, as equations, so each
defined output is a variable of the query and its value appears in models.
A definition is never a candidate for redundancy, nor reported in a
minimal set. `check::definitions` states the choice:

```fren
pub comp definitions {
    in kind: Kind
    pub det out substituted?     -- replaced by their definitions, rather than assumed as equations

    ensure rule: substituted? iff kind = Kind::Realizability

    expect never_searched: when kind = Kind::Realizability, substituted?
}
```

Both forms mean the same, since every definition determines its output.
Substituting everywhere would lose defined outputs' values in models;
using the equations in realizability would put defined outputs under `∃`.

## Expectations

For each expectation `e`, Fren asks whether `e` can be proved from `A`, `I`
and `R`. A model is a counterexample: Fren reports the values of the inputs
and public outputs in it.

If `A ∧ I ∧ R` is unsatisfiable, every expectation passes vacuously. The
realizability check then fails for the same component.

`check::expectation` gives the verdict, from the outcome `q` of the query:

```fren
pub comp expectation {
    in q: Outcome          -- can `e` be proved from A, I and R?
    pub det out verdict: Verdict
    pub det out reports_cex?

    ensure holds: when q = Unsat, verdict = Pass
    ensure refuted: when q = Sat, verdict = Fail
    ensure unknown: when q = Unknown, verdict = Inconclusive
    ensure report_cex: reports_cex? iff q = Sat
}
```

## Cover goals

A [cover goal](Lang/Components.md#cover-goals) `cover n: e` claims that
some behaviour meets the component and satisfies `e`: that

  A ∧ I ∧ R ∧ e

is satisfiable, with `D` among the hypotheses. Fren asks whether `not e`
can be proved from `A`, `I` and `R`. A model is a *witness*: a behaviour
that meets the component, in which the goal holds, and the goal passes.
If `not e` is proved, no behaviour meets the goal, and it fails
(`F0615`): Fren
reports a minimal set of assumptions and guarantees that rule it out,
as for [vacuity](#vacuity). If `A ∧ I ∧ R` is unsatisfiable, every cover
goal fails, with the realizability check.

So a cover goal is the converse of an expectation: an expectation holds if
its negation is impossible, a cover goal if it is possible. And the
vacuity check of a guarantee or expectation with the trigger `C` is the
cover goal `C`, with the same query. A cover goal is checked only in its
own component: an instance of the component does not check it again.

`check::cover_goal` gives the verdict and what is reported, from the outcome
`q` of the query:

```fren
pub comp cover_goal {
    in q: Outcome          -- can `not e` be proved from A, I and R?
    pub det out verdict: Verdict
    pub det out reports_witness?  -- report the model, in which the goal holds
    pub det out reports_core?     -- report the constraints that rule the goal out

    ensure met: when q = Sat, verdict = Pass
    ensure unmet: when q = Unsat, verdict = Fail
    ensure unknown: when q = Unknown, verdict = Inconclusive
    ensure report_witness: reports_witness? iff q = Sat
    ensure report_core: reports_core? iff q = Unsat

    expect pass_shows: when verdict = Pass, reports_witness?
    expect fail_explains: when verdict = Fail, reports_core?
}
```

### Query order

The query asks for a model, so a pass needs only the one query. The
minimal set is sought, by [deletion](#minimal-sets), only when the query
returns `Unsat`: its queries ask for no model.

## Global expectations

For a global expectation with binders `w_1: c_1`, ..., `w_n: c_n` and body
`E`, Fren asks whether `E` can be proved from the meanings `M_c_k(y_k)` of
the binders' components (see [Global expectations](Lang/Global.md#meaning)).
A model is a counterexample: Fren reports the values of the inputs and
public outputs of each binder, as `w_k.x`. `check::expectation` gives the
verdict, as for an expectation of a component.

If some `M_c_k` is unsatisfiable, the global expectation passes vacuously.
The realizability check then fails for `c_k`.

## Instance assumptions

For each instance `w` of a component `c`, and each assumption `a` of `c`,
and each input `x` of `c` whose type brings a constraint (see [Pattern
types](Lang/Components.md#pattern-types)), before its assumptions,
Fren asks whether `a`, or `x`'s constraint, with `w`'s bindings substituted, can be proved from
`A`, the bindings of `w`, and the constraints `I_v` of the instances `v`
declared before `w`. A model is a counterexample: Fren reports the values of
the inputs, and of the public outputs of the earlier instances.

`check::instance_assumption` decides each such query like an expectation:

```fren
pub comp instance_assumption {
    in q: Outcome          -- can it be proved from A, the bindings and earlier instances?
    pub det out verdict: Verdict
    pub det out reports_cex?

    inst as_expect: expectation { q }

    ensure like_expect: verdict = as_expect.verdict and (reports_cex? iff as_expect.reports_cex?)

    expect never_upgrades: when q = Unknown, verdict != Pass
}
```

## Vacuity

A guarantee or expectation whose [trigger](Lang/Components.md#triggers)
can never hold is satisfied vacuously, which usually indicates a mistake.
For each guarantee and expectation with a trigger, Fren asks whether `not
trigger` can be proved from `A`, `I` and `R`. For a global expectation, the
hypotheses are the meanings of its binders' components instead. If it can, the check fails,
and Fren reports a minimal set of assumptions and guarantees that rule
the trigger out. Constraints without a trigger, and assumptions, are not
checked.

`check::non_vacuity` gives the verdict, from the outcome `q` of the query:

```fren
pub comp non_vacuity {
    in q: Outcome          -- can `not trigger` be proved from A, I and R?
    pub det out verdict: Verdict

    ensure fires: when q = Sat, verdict = Pass
    ensure vacuous: when q = Unsat, verdict = Fail
    ensure unknown: when q = Unknown, verdict = Inconclusive
}
```

## Redundancy

An assumption or guarantee that follows from the component's other
constraints adds nothing to its meaning. If it is meant as a consequence,
it is better declared as an expectation, which the checks confirm rather
than take for granted.

For each assumption, Fren asks whether it can be proved from the other
assumptions. For each guarantee, Fren asks whether it can be proved from
`A`, `I` and the other guarantees. If it can, the check fails, and Fren
reports a minimal set of constraints it follows from. A redundant
constraint is not a mistake in itself, so the failure is a
[warning](View.md#severity), not an error.

An assumption is not compared with `I`, even though an instantiated
component's assumptions, through the instance's bindings, can constrain the
inputs: removing such an assumption would make the [instance
check](#instance-assumptions) fail.

Contradictory constraints entail everything, so the assumptions are not
checked if `A` is unsatisfiable, and the guarantees are not checked if
`A ∧ I ∧ R` is: the realizability check fails instead. Nor is a guarantee
checked if it failed the vacuity check, since a guarantee that never
applies always follows from the others. `check::redundancy_asked` gives
when a constraint is checked, from the outcome of asking whether `False`
can be proved from the constraints it would be compared with and itself
(`consistent_q`). That question is not asked once a vacuity query of the
component has answered `Sat`. That query's hypotheses are `A`, `I`, `R` and
a trigger, so `A ∧ I ∧ R`, and `A` with it, are satisfiable, and
`consistent_q` is `Sat` for both.

```fren
pub comp redundancy_asked {
    in consistent_q: Outcome
    in vacuous?            -- it failed the vacuity check
    pub det out asked?

    ensure asked: asked? iff (consistent_q != Unsat and not vacuous?)
}
```

`check::non_redundancy` gives the verdict, from the outcome `q` of the
query:

```fren
pub comp non_redundancy {
    in q: Outcome          -- can the constraint be proved from the others?
    pub det out verdict: Verdict

    ensure independent: when q = Sat, verdict = Pass
    ensure redundant: when q = Unsat, verdict = Fail
    ensure unknown: when q = Unknown, verdict = Inconclusive
}
```

## Definedness

An index `q[i]` is unspecified unless `0 <= i < q.len` (see
[Expressions](Lang/Expressions.md#sequences)): the checks hold for every
value it could have, so an out-of-range index is sound, but the constraint
then says nothing useful there, which is almost always a mistake. For each
index in a constraint, a definition or a binding, with its guard `G`, Fren
asks whether `0 <= i < q.len` can be proved from `G` and the
hypotheses of where it is written:

| Where | Hypotheses |
|---|---|
| an assumption | the other assumptions |
| a guarantee, expectation, cover goal or definition | `A`, `I` and `R`, as for vacuity |
| a binding of an instance | `A`, and the instances declared before it |
| a global expectation | the meanings of its binders' components |
| a precondition of a function | the function's other preconditions |
| a function's body or postcondition | the function's preconditions |
| the value of a constant | none |

A guarantee's own `R` is among its hypotheses, so a guarantee can
ensure its own definedness through another, such as `ensure long: q.len >
3` beside `ensure third: q[3] = x`: the system meets both or neither. A
component with no index has no definedness results. `check::definedness`
decides each query like an expectation, and a model is a counterexample,
reported at the `[` of the index:

```fren
pub comp definedness {
    in q: Outcome          -- can `0 <= i < q.len` be proved from the guard and the hypotheses?
    pub det out verdict: Verdict
    pub det out reports_cex?

    inst as_expect: expectation { q }

    ensure like_expect: verdict = as_expect.verdict and (reports_cex? iff as_expect.reports_cex?)
}
```

## Pattern types

The pattern-type check is part of [definedness](#definedness), whose
results it gives. A value given where a [pattern type](Lang/Types.md#pattern-types) is
declared has an *obligation*: it must match the pattern. For each value
given where a pattern type is declared, at the top of the declared type or
in an element type (a definition, an argument of a function, a field of a
record literal or update, a value of a payload, a typed `let` or `where`
definition, a defined function's body, or a constant's value), with its
guard `G`, Fren asks whether the value matches, as `e is P`, or for an
element type, whether each element does, can be proved from `G` and the
hypotheses of where it is written, as for [definedness](#definedness): in
the body of a defined function or the value of a constant, `G` and `N`
over the function's parameters, which assumes that the parameters match
their own pattern types. An instance's binding is checked instead by the
[instance check](#instance-assumptions). A component or item with no
such value has no pattern-type results. `check::pattern_obligation`
decides each query like an expectation, and a model is a counterexample,
reported at the value:

```fren
pub comp pattern_obligation {
    in q: Outcome          -- can `e is P` be proved from the guard and the hypotheses?
    pub det out verdict: Verdict
    pub det out reports_cex?

    inst as_expect: expectation { q }

    ensure like_expect: verdict = as_expect.verdict and (reports_cex? iff as_expect.reports_cex?)
}
```

## Completeness

A [`match`](Lang/Expressions.md#matches) in which no arm is taken has no
specified value, as an index out of range has none: the checks hold for
every value it could have there, so the constraint then says nothing
useful. The static rules make every `match` exhaustive when its guards are
ignored, so this can happen only in one whose arms without guards are not
exhaustive, and for each such `match`, Fren asks whether some arm is
always taken. A [table](Lang/Expressions.md#tables) is such a `match`,
each of whose rows other than `_` has a guard: it is asked about exactly
when it has no `_` row. `check::completeness_asked` gives which are asked
about:

```fren
pub comp completeness_asked {
    in unguarded_exhaustive?  -- its arms without guards are exhaustive
    pub det out asked?

    ensure rule: asked? iff not unguarded_exhaustive?

    -- A `match` without guards, or a table with a `_` row, is never asked about.
    expect without_guards: when unguarded_exhaustive?, not asked?
}
```

Whether the arms without guards are exhaustive is decided by the
[usefulness](Lang/Patterns.md#usefulness) of `_` after them. Where every
pattern is flat, `_`, a binder or a variant without a payload, `_`'s
usefulness comes to this: the arms without guards are exhaustive exactly
when one of them matches every value, or each variant is named by one of
them. `check::flat_completeness_asked` states it of a `match` on an
enumeration of three such variants, `A`, `B` and `C`, from its arms in
order, each `_` or a variant, with a guard or without, and
`flat_completeness_refines` confirms that it refines `completeness_asked`.
Patterns that are nested, literals or ranges, and payloads, are left to
`lang::usefulness`. Membership in a sequence is outside the decidable
core, though the solver decides these:

```fren
pub enum FlatArm { Wild, A, B, C, GuardedWild, GuardedA, GuardedB, GuardedC }

set_option fren.lint.undecidable "allow" in
pub comp flat_completeness_asked {
    use self::FlatArm::{A, B, C, Wild}
    in arms: Seq(FlatArm)    -- the arms, in order
    pub out asked?

    ensure rule: asked? iff not (Wild in arms or (A in arms and B in arms and C in arms))

    -- An arm with a guard names nothing: a `match` that needs it is asked about.
    expect guarded_needed: when arms = [FlatArm::GuardedA, B, C], asked?
}

set_option fren.lint.undecidable "allow" in
refine flat_completeness_refines: flat_completeness_asked refines completeness_asked {
    unguarded_exhaustive? := FlatArm::Wild in arms or (FlatArm::A in arms and FlatArm::B in arms and FlatArm::C in arms),
}
```

With the arms' patterns `P_1`, ..., `P_n`, their guards `C_1`, ...,
`C_n` (`true` for an arm without one; for a table, the patterns are `_`
and the guards its rows' conditions), and the `match`'s guard `G`, the
conditions under which it is evaluated (read as an index's are, see
[Sequences](Lang/Expressions.md#sequences)), Fren asks whether `(P_1 and
C_1) or ... or (P_n and C_n)` can be proved from `G` and the hypotheses of
where the `match` is written, as for [definedness](#definedness). In the
body of a defined function, there are no hypotheses but `G`, `N` and
the function's preconditions, over its parameters, and in the value of a
constant only `G` and `N`: a function's body is checked for every argument
that meets its preconditions, not only those that a component passes it. `check::completeness` decides each query like an expectation, and a
model is a counterexample, a value of the variables for which no arm is
taken, reported at the `match`'s `match` (`F0625`), or at the table's
`table` (`F0618`):

```fren
pub comp completeness {
    in q: Outcome          -- can `(P_1 and C_1) or ... or (P_n and C_n)` be proved from the guard and the hypotheses?
    pub det out verdict: Verdict
    pub det out reports_cex?

    inst as_expect: expectation { q }

    ensure like_expect: verdict = as_expect.verdict and (reports_cex? iff as_expect.reports_cex?)
}
```

## Disjointness

A table's value is its first row's that holds, so where two rows hold at
once, the order of its rows decides its value, which is easy to misread.
For each two rows `i < j` of a table, other than a `_` row, with the
conditions `C_i` and `C_j` and the table's guard `G`, Fren asks whether
`not (D_i and D_j and C_i and C_j)` can be proved from `G` and the
hypotheses of where the table is written, as for
[completeness](#completeness). `D_i` says that the indexes in `C_i` are in
range where `C_i` evaluates them, under the guards within `C_i` alone (see
[Sequences](Lang/Expressions.md#sequences)), and is `true` if it has none.
A row's condition is evaluated only where the earlier rows' fail, so an
index in it may rest on them: in `table { q = [] => 0, q[0] > 0 => 1, _
=> 2 }`, `q[0]` is defined wherever it is evaluated, and the two rows do
not overlap, though `q[0] > 0` could hold of the unknown value of `[][0]`.
Each pair is its own check, so the message can name both rows. `check::disjointness`
decides each query like an expectation, and a model is a witness, a value
of the variables for which both rows hold, reported at the condition of
the later row:

```fren
pub comp disjointness {
    in q: Outcome          -- can `not (D_i and D_j and C_i and C_j)` be proved from the guard and the hypotheses?
    pub det out verdict: Verdict
    pub det out reports_witness?

    inst as_expect: expectation { q }

    ensure like_expect: verdict = as_expect.verdict and (reports_witness? iff as_expect.reports_cex?)
}
```

A `_` row holds wherever no earlier row does, so it overlaps none, and is
in no disjointness check. The checks of a table are on its conditions
alone: a row's value can be the same as another's, and the rows still
overlap. Only tables are checked for disjointness: the arms of a `match`
are told apart by their patterns first, and an arm with a guard is
usually followed by one that its guard's failure leads to, as in `Eq if
bound = 0 => AtStart, Eq => Other`.

## Reachability

An arm of a [`match`](Lang/Expressions.md#matches) that is never taken
where the `match` is evaluated is dead, which usually indicates a mistake:
its guard can never hold, or the arms before it take every case it would.
The static rules already reject an arm that the patterns of the arms
before it without guards cover. Whether a guard holds is left to this
check, which asks about each arm that has a guard or follows an arm that
has one. Every row of a [table](Lang/Expressions.md#tables) is such an arm,
but a table whose only row is `_`. `check::reachability_asked` gives which
arms are asked about:

```fren
pub comp reachability_asked {
    in guarded?              -- the arm has a guard
    in after_guard?          -- some arm before it has a guard
    pub det out asked?

    ensure rule: asked? iff (guarded? or after_guard?)

    -- An arm of a `match` without guards is never asked about.
    expect static_only: when not guarded? and not after_guard?, not asked?
}
```

`check::arms_asked` states the same over the arms of a `match` as
written, in order, each with a guard or without, and
`arms_asked_refines` confirms that it refines `reachability_asked`, its
arm `j` having a guard where `guarded?` says, and an arm before it having
one where `after_guard?` says. An arm is asked about exactly when the
first arm with a guard is at or before it:

```fren
pub enum GuardOf { Unguarded, Guarded }

set_option fren.lint.undecidable "allow" in
pub comp arms_asked {
    use self::GuardOf::Guarded
    in guards: Seq(GuardOf)  -- whether each arm has a guard, in order
    in j: Int                -- the arm asked about, by its position
    pub out asked?

    ensure rule: asked? iff 0 <= guards.index_of([Guarded], 0) <= j
}

set_option fren.lint.undecidable "allow" in
refine arms_asked_refines: arms_asked refines reachability_asked {
    guarded? := 0 <= j < guards.len and guards[j] = GuardOf::Guarded,
    after_guard? := 0 <= guards.index_of([GuardOf::Guarded], 0) < j,
}
```

For arm `j`, with `P_k` and `C_k` as for [completeness](#completeness),
`T_k` for `P_k and C_k`, that arm `k` is taken if no arm before it is,
`F_j` for `not T_1 and ... and not T_(j-1)`, and the `match`'s guard `G`,
Fren asks whether `not (F_j and T_j)` can be proved from `G` and the
hypotheses of where the `match` is written, as for
[completeness](#completeness), but without the constraint, definition
or binding that the `match` is in. That constraint holds of a behaviour
only where its `match` has the value it needs, so it would rule out the
arms whose values it does not need: in `ensure r: match k { Kind::A if
ok? => true, _ => false }`, `r` holds only where the first arm is taken,
yet the last arm is how `r` says what it rules out, and is not dead. If
it can be proved, no behaviour that the other hypotheses allow
takes the arm, and the check fails, at the arm's pattern (`F0626`), or, for
a table, at the row's condition or its `_` (`F0627`). So a guard that is
`false`, or that contradicts the arm's pattern or the hypotheses, fails it,
and so does an arm after others that take every case it would, as `x >= 0`
after `x > 0` and `x = 0` does, or a table's `_` row after rows of which
one always holds. `check::reachability` decides each query like
[vacuity](#vacuity), whose query also asks whether something can hold:

```fren
pub comp reachability {
    in q: Outcome          -- can `not (F_j and T_j)` be proved from the guard and the hypotheses?
    pub det out verdict: Verdict

    inst as_vacuity: non_vacuity { q }

    ensure like_vacuity: verdict = as_vacuity.verdict
}
```

A model is a behaviour that takes the arm, which is not reported: a pass
is silent.

`check::split_questions` states what the goals of these questions are,
in each behaviour, from what each arm of the `match` does there, as
[`lang::guarded_match`](Lang/Expressions.md#matches) has it, with its
`ArmAt` again here. The goal of
arm `j`'s reachability is that `j` is not the arm taken, so the check
fails exactly when no behaviour that the hypotheses allow takes it; the
goal of completeness is that some arm is taken. Of a table, each row is
`Taken` where its condition holds, else `GuardFails`, and a `_` row is
`Taken`. The arm taken is found as there, and `k` stands for any
position, as there:

```fren
pub enum ArmAt { NoMatch, GuardFails, Taken }

set_option fren.lint.undecidable "allow" in
pub comp split_questions {
    use self::ArmAt::Taken
    in arms: Seq(ArmAt)      -- what each arm does here, in order
    in j: Int                -- the arm whose reachability is asked about
    in k: Int                -- any position, for `none_before`
    pub out first: Int := arms.index_of([Taken], 0)  -- the position of the arm taken, `-1` if none is
    pub out reach_goal?      -- the goal of arm `j`'s reachability question here
    pub out complete_goal?   -- the goal of the completeness question here

    assume an_arm: 0 <= j < arms.len

    ensure reach: reach_goal? iff first != j
    ensure complete: complete_goal? iff first >= 0

    expect in_range: -1 <= first < arms.len
    expect first_taken: when first >= 0, arms[first] = Taken
    expect none_before: when 0 <= k < arms.len and (first = -1 or k < first), arms[k] != Taken

    -- Arm `j` is reachable here exactly when it is taken here.
    expect taken_here: when not reach_goal?, arms[j] = Taken
}
```

Completeness, disjointness and reachability ask one query each, as
definedness does, so they have no query order of their own, and their
queries, like definedness's, are quantifier-free. Their hypotheses are those of
definedness, `N` among them (see the [table above](#definedness)): a
guarantee's own `R` is among its hypotheses, so a table or a `match` in a
guarantee may be complete only because another guarantee rules out
the cases it leaves out, and an arm of one may be unreachable because
another guarantee rules out every behaviour that takes it. Reachability
alone leaves out the constraint, definition or binding that the `match`
or table is in, as above: a definition's equation in `D` too, so that in
`out y: Int := match x { n if n > 0 => 1, _ => 2 }` beside `ensure q: y =
1`, the last arm is reachable, as it would be in an `ensure`. For an
assumption, and a binding, whose instance is not among its hypotheses,
that is already so.
`check::reach_hypothesis` states which of the hypotheses of definedness
reachability asks under:

```fren
pub comp reach_hypothesis {
    in definedness?          -- the hypothesis is one of the definedness check's at the `match`
    in enclosing?            -- it is the constraint, definition or binding that the `match` is in
    pub det out used?

    ensure rule: used? iff (definedness? and not enclosing?)
}
```

`check::reach_hypotheses` states the same over the hypotheses that the
check is built from, in order: each one of definedness's at the case
other than the item that the case is in (`Definedness`), that item
(`Enclosing`), or none of definedness's (`Other`). Reachability asks
under the hypotheses at the positions where `used?` holds, and
`reach_hypotheses_refines` confirms that it refines `reach_hypothesis`:

```fren
pub enum HypAt { Definedness, Enclosing, Other }

pub comp reach_hypotheses {
    use self::HypAt::Definedness
    in hyps: Seq(HypAt)      -- the hypotheses, in order
    in k: Int                -- a hypothesis, by its position
    pub out used?            -- reachability asks under hypothesis `k`

    ensure rule: used? iff (0 <= k < hyps.len and hyps[k] = Definedness)

    -- The item that the case is in is never among them.
    expect not_enclosing: when 0 <= k < hyps.len and hyps[k] = HypAt::Enclosing, not used?
}

refine reach_hypotheses_refines: reach_hypotheses refines reach_hypothesis {
    definedness? := 0 <= k < hyps.len and hyps[k] != HypAt::Other,
    enclosing? := 0 <= k < hyps.len and hyps[k] = HypAt::Enclosing,
}
```

## Preconditions

For each application `f(a_1, ..., a_n)` of a function `f` with
[preconditions](Lang/Items.md#contracts), with its guard `G`, and each
precondition `P` of `f`, Fren asks whether `P`, with the arguments for the
parameters, can be proved from `G` and the hypotheses of where the
application is written, as for [definedness](#definedness): this is the
[instance check](#instance-assumptions) for a function. The guard is read
as an index's is (see [Sequences](Lang/Expressions.md#sequences)), so in
`kind(t) = SetTy and elem(t) = u`, `elem(t)` is evaluated only where
`kind(t) = SetTy`. An application in a precondition of another function
`g` is checked under `g`'s other preconditions, and one in `g`'s body or
postconditions under all of them, for every value of `g`'s parameters
that meets them. Each application and precondition is its own check, so
the message can name the precondition. `check::precondition` decides each
query like an expectation, and a model is a counterexample, reported at
the name of the applied function:

```fren
pub comp precondition {
    in q: Outcome          -- can `P(a_1, ..., a_n)` be proved from the guard and the hypotheses?
    pub det out verdict: Verdict
    pub det out reports_cex?

    inst as_expect: expectation { q }

    ensure like_expect: verdict = as_expect.verdict and (reports_cex? iff as_expect.reports_cex?)
}
```

`check::precondition_at` states the check in detail, over the domain of
[realizability](#contracts-of-uninterpreted-functions): an application
whose arguments may be either argument, of a function whose precondition
holds at the arguments `pres`, evaluated where its guard holds, at the
arguments `guarded`. Its implementation asks the question that both front
ends build (`check::application_contract`) with the real check, and a
solver that tries every argument. It refines `check::precondition`, whose
query is proved exactly when every guarded argument meets the
precondition:

```fren
pub comp precondition_at {
    in pres: Set(Argument)      -- the arguments that meet the precondition
    in guarded: Set(Argument)   -- the arguments where the application's guard holds
    pub det out verdict: Verdict
    pub det out reports_cex?

    ensure rule: verdict = (if guarded subset pres then Pass else Fail)
    ensure cex: reports_cex? iff verdict = Fail

    expect unguarded: when guarded = {}, verdict = Pass
}

refine precondition_detail: precondition_at refines precondition { q := if guarded subset pres then Unsat else Sat }
```

A precondition that fails is reported, and nothing more: the
application's value is still the body's, for a defined function, or
unknown, for an uninterpreted one, so a check that rests on it holds for
every value the application could have, as for an index out of range.

`check::application_contract` states what an application means to the
checks, from the values, at its arguments, of the applied function's
clauses, in order, and whether its guard holds: it asks a question of each
precondition, whose goal holds where the guard fails or the precondition
holds; and an application of an uninterpreted function brings a fact of
each postcondition to its queries, which holds where some precondition
fails or the postcondition holds (see [Postconditions](#postconditions)).
`k` is any clause, so the rule is checked for each. Both front ends build
the questions and facts with the same functions, which its implementation
runs on these values. Membership in a sequence of unknown length, as
`false in pres`, is outside the [decidable core](Lang/Decidability.md),
so the component opts out:

```fren
set_option fren.lint.undecidable "allow" in
pub comp application_contract {
    in pres: Seq(Bool)     -- the function's preconditions, in order, at the arguments
    in posts: Seq(Bool)    -- its postconditions, in order, at the arguments and the application's value
    in guarded?            -- the application's guard holds
    in k: Int              -- any clause
    pub det out asks?      -- the application asks a question of precondition `k`
    pub det out question?  -- the question's goal holds
    pub det out brings?    -- the application brings a fact of postcondition `k`
    pub det out fact?      -- the fact holds

    ensure asked: asks? iff 0 <= k < pres.len
    ensure question: question? iff (asks? and (not guarded? or pres[k]))
    ensure brought: brings? iff 0 <= k < posts.len
    ensure fact: fact? iff (brings? and (false in pres or posts[k]))

    expect unguarded: when asks? and not guarded?, question?
    expect met: when brings? and not (false in pres), fact? iff posts[k]
    expect vacuous: when brings? and false in pres, fact?
}
```

## Postconditions

For each postcondition `Q` of a [defined
function](Lang/Items.md#defined-functions), Fren asks whether `Q` can be
proved from the function's preconditions, with its parameters free: a
claim about the body, which the solver sees through the function's
definition, as an expectation is a claim about a component. The query
has no quantifier, since the parameters are its variables. A model is a
counterexample, the values of the parameters, reported at the
postcondition's name. An uninterpreted function's postconditions are not
checked: they are what is known of it, which each application brings to
its queries as `N` (see [above](#checks)), and an
[interpretation](Impl.md#interpretations) in Lean proves them.
`check::postcondition` decides each query like an expectation:

```fren
pub comp postcondition {
    in q: Outcome          -- can `Q` be proved from the function's preconditions?
    pub det out verdict: Verdict
    pub det out reports_cex?

    inst as_expect: expectation { q }

    ensure like_expect: verdict = as_expect.verdict and (reports_cex? iff as_expect.reports_cex?)
}
```

`check::postcondition_at` states it in detail, over the same domain: a
defined function whose preconditions hold at the arguments `pres`, and
whose postcondition holds, of the body's value, at the arguments `posts`.
Its implementation builds the body's component with the function's
preconditions and postcondition, and runs the real check, with a solver
that tries every argument. It refines `check::postcondition`:

```fren
pub comp postcondition_at {
    in pres: Set(Argument)    -- the arguments that meet the preconditions
    in posts: Set(Argument)   -- the arguments where the postcondition holds
    pub det out verdict: Verdict
    pub det out reports_cex?

    ensure rule: verdict = (if pres subset posts then Pass else Fail)
    ensure cex: reports_cex? iff verdict = Fail

    expect everywhere: when posts = {Argument::A0, Argument::A1}, verdict = Pass
}

refine postcondition_detail: postcondition_at refines postcondition { q := if pres subset posts then Unsat else Sat }
```

## Minimal sets

Realizability, vacuity and redundancy report a *minimal* set of
constraints: one that entails the failure, of which no constraint can be
dropped and still entail it. Fren finds it by deletion: it tries to drop
each constraint in turn, and keeps the drop if the rest still entail the
failure. `check::minimal` states what minimal means, of a candidate `core`
of the `candidates`, where `refutes?` says whether a set of constraints
entails the failure, with the goal negated where there is one. Every
member that may be `dropped` is an input, so the rule is checked for each
of them, which is what quantifying over the core's members means:

```fren
pub type ConstraintName

pub fn refutes?(Set(ConstraintName))   -- the constraints entail the failure

set_option fren.lint.undecidable "allow" in
pub comp minimal {
    in candidates: Set(ConstraintName)
    in core: Set(ConstraintName)
    in dropped: ConstraintName          -- any one constraint, for the minimality condition
    pub det out minimal?

    ensure rule: minimal? iff (core subset candidates and refutes?(core)
        and (when dropped in core, not refutes?(core minus {dropped})))

    expect within: when minimal?, core subset candidates
    expect entails: when minimal?, refutes?(core)
    -- A core that still refutes without one of its constraints is not minimal.
    expect smaller_refutes: when dropped in core and refutes?(core minus {dropped}), not minimal?
}
```

A function of sets of an abstract type is outside the [decidable
core](Lang/Decidability.md#sets), so `minimal` opts out. Deletion meets
`minimal?` only when every query is answered: an `Unknown` answer keeps the
constraint, so the set may then not be minimal.

## Determinism

An output declared with `det out` (see [Components](Lang/Components.md#members))
must be determined by the component's inputs: any two behaviours that
satisfy `I` and `R` on the same admissible input agree on it. For each `det
out` `x`, Fren takes a second copy `y'`, `o'` of the instance variables and
outputs, and asks whether `x = x'` can be proved from

  A(i) ∧ I(i, y) ∧ R(i, y, o) ∧ I(i, y') ∧ R(i, y', o')

The instance variables are copied too, so an output that depends on an
instance's output which is not itself determined is not determined either.
The functions are not copied: both copies are under the same
[interpretation](#interpretations), so an output that is a function of the
inputs, as in `ensure r: x = f(i)`, is determined. `check::copied` gives what
the second copy renames:

```fren
pub enum Symbol { Input, InstanceVariable, Output, Function }

pub comp copied {
    in symbol: Symbol
    pub det out copied?

    ensure rule: copied? iff symbol is Symbol::InstanceVariable | Symbol::Output

    expect shared_interpretation: when symbol = Symbol::Function, not copied?
}
```

A model is a counterexample: Fren reports the inputs, and the two values of
`x`.

`check::determinism` decides each query like an expectation:

```fren
pub comp determinism {
    in q: Outcome          -- can `x = x'` be proved from both copies?
    pub det out verdict: Verdict
    pub det out reports_cex?

    inst as_expect: expectation { q }

    ensure like_expect: verdict = as_expect.verdict and (reports_cex? iff as_expect.reports_cex?)
}
```

## Checking by testing

Some checks are beyond what the solver decides in practice (see
[Decidability](Lang/Decidability.md#in-practice)). A spec may say so where
it applies, and have such a check tested instead, as `fren quickcheck`
tests it (see [Evaluation](Eval.md#fren-quickcheck)):

```
item   := evidence-setting ["in" item] | ...
member := evidence-setting "in" member | ...
evidence-setting := "set_option" "fren.evidence" STRING
```

`set_option fren.evidence "tested" in` before a component, an expectation
or global expectation, an instance or a `det out` sets the evidence of its
checks to *testing*; `"solver"`, the default, sets it back. Before a
component, it sets that of all the component's checks, and before a member,
that of the member's checks, which takes precedence:

| Before | Its checks |
|---|---|
| an expectation | the expectation, its vacuity, and the definedness, completeness, disjointness, reachability and preconditions of what it reads |
| a cover goal | the cover goal, and the definedness, completeness, disjointness, reachability and preconditions of what it reads |
| an instance | the instance's assumptions, and the definedness, completeness, disjointness, reachability and preconditions of its bindings |
| a `det out` | its determinism |
| a component | all of the component's checks |
| a global expectation | its expectation, its vacuity, and the definedness, completeness, disjointness, reachability and preconditions of what it reads |
| a [refinement](Lang/Refinement.md) | all of the checks of its obligation, including the definedness of the bindings of the abstract component's instances |

As with a [lint setting](Lint.md), `set_option` without `in` sets the
evidence of every later component, global expectation and
[refinement](Lang/Refinement.md) in the file, and
before any other item it sets nothing. Within a component, the setting must
be followed by `in` and by a member whose checks it sets: before anything
else, such as a guarantee, it is an error (`F0215`), and so is a
`set_option` of any other option before a member (`F0216`). The setting is a
statement that the solver cannot be relied on there, so it is never
reported as unneeded. A value other than `"tested"` or `"solver"` is an
error (`F0214`), reported once, at the value, wherever the setting is.
The items and members after it are elaborated as though it were
`"solver"`, so that the error is not repeated at each of them.

`fren check` asks the solver nothing about a check whose evidence is
testing. It tests the check with `--tests` tests (default 100) from
`--seed` (default 0), and reports the result as `fren quickcheck` does
(`eval::test_verdict`): a counterexample fails the check, and testing that
reaches no conclusion leaves it inconclusive, with the same warnings. The
checks that testing cannot decide are not run: vacuity and redundancy,
which ask whether something can hold at all, which a failed search does
not refute; definedness, since an index out of range has no value
that the evaluator knows (see [Evaluation](Eval.md#searching-for-behaviours)),
so testing can neither pass nor fail it; completeness, disjointness and
reachability, which, like definedness, are about where an expression is
evaluated: a test only reaches behaviours in which the constraints have
values, and a table or `match` where no row or arm is taken has none, so
testing could never find a counterexample to completeness, and the checks
of a table or `match` are run together; and preconditions, which, like
definedness, are about where an application is evaluated, and whose
failure leaves the application's value unknown. A test that reaches
an expectation shows that its trigger can hold, which is what its vacuity
check would show. A cover goal asks whether something can hold too, but
testing can pass it: a test that finds a behaviour that meets the
component, in which the goal holds, is a witness, and passes it. Testing
that finds none leaves the goal inconclusive, with a warning (`F0616`),
since a failed search does not show that no behaviour exists; it never
fails a goal. The summary counts the passes that came from testing:

```text
fren: 30 passed (2 by testing), 0 failed, 0 inconclusive, 0 redundant
```

Lean has no evaluator, so `#fren_check` does not run a check whose evidence
is testing: it reports, as information, that `fren check` tests it. Such a
check is not part of the [agreement with Lean](Cli.md#agreement-with-lean).

`check::by_testing` gives how a check is run:

```fren
pub enum Run { BySolver, ByTesting, Skipped }

pub comp by_testing {
    use self::Kind::{
        Completeness,
        Definedness,
        Disjointness,
        Precondition,
        Reachability,
        Redundancy,
        Vacuity,
    }
    use self::Run::{BySolver, ByTesting, Skipped}
    in kind: Kind
    in tested?             -- the check's evidence is testing
    pub det out run: Run

    ensure rule: run = table {
        | not tested? => BySolver,
        | tested? and not kind in {Vacuity, Redundancy, Definedness, Completeness, Disjointness, Precondition, Reachability} => ByTesting,
        | tested? and kind in {Vacuity, Redundancy, Definedness, Completeness, Disjointness, Precondition, Reachability} => Skipped,
    }

    expect never_both: when tested?, run != BySolver
}
```

## Verdict families

Each check that reaches its verdict from one outcome refines `proved` or
`satisfiable`: the checks that prove something, and the checks that ask
whether something can hold.

```fren
refine expectation_proves: expectation refines proved
refine instance_assumption_proves: instance_assumption refines proved
refine definedness_proves: definedness refines proved
refine completeness_proves: completeness refines proved
refine disjointness_proves: disjointness refines proved
refine precondition_proves: precondition refines proved
refine postcondition_proves: postcondition refines proved
refine determinism_proves: determinism refines proved
refine vacuity_witnesses: non_vacuity refines satisfiable
refine cover_witnesses: cover_goal refines satisfiable
refine redundancy_witnesses: non_redundancy refines satisfiable
refine reachability_witnesses: reachability refines satisfiable

#fren_check
```
