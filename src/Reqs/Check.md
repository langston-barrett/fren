# Checks

Fren checks each component six ways:

| Check | Reported as | Confirms |
|---|---|---|
| [Realizability](#realizability) | `realizable` | some system can meet the requirements, for every admissible input |
| [Expectations](#expectations) | `expect` | each expectation follows from the assumptions and requirements |
| [Instance assumptions](#instance-assumptions) | `instance` | each instance's bindings satisfy the instantiated component's assumptions |
| [Vacuity](#vacuity) | `vacuity` | the trigger of each requirement and expectation can hold |
| [Redundancy](#redundancy) | `redundancy` | no assumption or requirement follows from the others |
| [Determinism](#determinism) | `determinism` | each `det out` is determined by the inputs |

A [global expectation](Lang/Global.md) is checked two of these ways: the
[expectation check](#global-expectations) confirms that it holds, and the
[vacuity check](#vacuity) that its trigger can hold.

The formulas below use the notation of [Components](Lang/Components.md#meaning):
`A` is the conjunction of the component's assumptions, `R` of its
requirements, and `I` of its instances, over the inputs `i`, the instances'
variables `y` and the outputs `o`.
`D` is the equations `d = e` of the component's [defined
outputs](Lang/Components.md#defined-outputs), and `o` excludes them.

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
for the `fren` command; the default is 10 seconds.

From the solver's outcomes, each check reaches a verdict: `Pass`, `Fail` or
`Inconclusive`. An `Unknown` outcome never leads to `Pass`. Results are
trusted from the solver: no Lean proofs of them are produced.

```fren
pub enum Outcome { Sat, Unsat, Unknown }

pub enum Verdict { Pass, Fail, Inconclusive }

pub enum Kind { Realizability, Expectation, InstanceAssumption, Vacuity, Redundancy, Determinism, Definedness }

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

    req proof: verdict = Pass iff q = Unsat
    req counterexample: verdict = Fail iff q = Sat

    expect conservative: when q = Unknown, verdict = Inconclusive
}

pub comp satisfiable {
    in q: Outcome          -- can the negation of the goal be proved?
    pub det out verdict: Verdict

    req witness: verdict = Pass iff q = Sat
    req refuted: verdict = Fail iff q = Unsat

    expect conservative: when q = Unknown, verdict = Inconclusive
}
```

`check::applies` gives which checks run on an item. A global expectation
constrains nothing, so there is nothing to realize, determine or find
redundant, and its binders' inputs have no obligations:

```fren
pub comp applies {
    use self::Kind::{Definedness, Determinism, Expectation, Realizability, Vacuity}
    in global?             -- a global expectation, rather than a component
    in kind: Kind
    pub det out runs?

    req components: unless global?, runs?
    req globals: when global?, runs? iff kind in {Expectation, Vacuity, Definedness}

    expect claims_only: when global? and runs?, not kind in {Realizability, Determinism}
}
```

## Realizability

A component is realizable if some system can respond to every admissible
input, whatever its instances do:

  ∀ i y. A(i) ∧ I(i, y) ⇒ ∃ o. R(i, y, o)

with each defined output replaced by its definition (see
[Definitions](#definitions)).

Fren asks two queries:

- **Assumptions.** Can `False` be proved from `A`? If so, the assumptions
  are contradictory, so the formula above holds vacuously, and the check
  fails rather than passing. Fren reports a minimal set of contradictory
  assumptions.
- **Counterexample.** Can `∃ o. R(i, y, o)` be proved from `A` and `I`, with
  the inputs and instance variables free? A model is an input, together
  with a behaviour of the instances, that no system could answer. Fren
  reports it, with a minimal set of requirements that conflict on it.

`check::realizability` gives the verdict and what is reported, from the
outcomes of the two queries (`assume_q` and `cex_q`):

```fren
pub comp realizability {
    in assume_q: Outcome   -- can `False` be proved from A?
    in cex_q: Outcome      -- can `exists outputs, R` be proved from A and I?
    pub det out verdict: Verdict
    pub det out reports_cex?   -- report the input and the conflicting requirements
    pub det out reports_vacuous?  -- report that the assumptions are contradictory

    req vacuous: when assume_q = Unsat, verdict = Fail
    req cex: when assume_q != Unsat and cex_q = Sat, verdict = Fail
    req pass: when assume_q = Sat and cex_q = Unsat, verdict = Pass
    req unknown_cex: when assume_q != Unsat and cex_q = Unknown, verdict = Inconclusive
    req unknown_assume: when assume_q = Unknown and cex_q = Unsat, verdict = Inconclusive
    req report_cex: reports_cex? iff (assume_q != Unsat and cex_q = Sat)
    req report_vacuous: reports_vacuous? iff assume_q = Unsat

    expect never_upgrades: when assume_q = Unknown or cex_q = Unknown, verdict != Pass
    expect fail_explains: when verdict = Fail, reports_cex? or reports_vacuous?
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

    req rule: substituted? iff kind = Kind::Realizability

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

    req holds: when q = Unsat, verdict = Pass
    req refuted: when q = Sat, verdict = Fail
    req unknown: when q = Unknown, verdict = Inconclusive
    req report_cex: reports_cex? iff q = Sat
}
```

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
Fren asks whether `a`, with `w`'s bindings substituted, can be proved from
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

    req like_expect: verdict = as_expect.verdict and (reports_cex? iff as_expect.reports_cex?)

    expect never_upgrades: when q = Unknown, verdict != Pass
}
```

## Vacuity

A requirement or expectation whose [trigger](Lang/Components.md#triggers)
can never hold is satisfied vacuously, which usually indicates a mistake.
For each requirement and expectation with a trigger, Fren asks whether `not
trigger` can be proved from `A`, `I` and `R`. For a global expectation, the
hypotheses are the meanings of its binders' components instead. If it can, the check fails,
and Fren reports a minimal set of assumptions and requirements that rule
the trigger out. Constraints without a trigger, and assumptions, are not
checked.

`check::non_vacuity` gives the verdict, from the outcome `q` of the query:

```fren
pub comp non_vacuity {
    in q: Outcome          -- can `not trigger` be proved from A, I and R?
    pub det out verdict: Verdict

    req fires: when q = Sat, verdict = Pass
    req vacuous: when q = Unsat, verdict = Fail
    req unknown: when q = Unknown, verdict = Inconclusive
}
```

## Redundancy

An assumption or requirement that follows from the component's other
constraints adds nothing to its meaning. If it is meant as a consequence,
it is better declared as an expectation, which the checks confirm rather
than take for granted.

For each assumption, Fren asks whether it can be proved from the other
assumptions. For each requirement, Fren asks whether it can be proved from
`A`, `I` and the other requirements. If it can, the check fails, and Fren
reports a minimal set of constraints it follows from. A redundant
constraint is not a mistake in itself, so the failure is a
[warning](View.md#severity), not an error.

An assumption is not compared with `I`, even though an instantiated
component's assumptions, through the instance's bindings, can constrain the
inputs: removing such an assumption would make the [instance
check](#instance-assumptions) fail.

Contradictory constraints entail everything, so the assumptions are not
checked if `A` is unsatisfiable, and the requirements are not checked if
`A ∧ I ∧ R` is: the realizability check fails instead. Nor is a requirement
checked if it failed the vacuity check, since a requirement that never
applies always follows from the others. `check::redundancy_asked` gives
when a constraint is checked, from the outcome of asking whether `False`
can be proved from the constraints it would be compared with and itself
(`consistent_q`):

```fren
pub comp redundancy_asked {
    in consistent_q: Outcome
    in vacuous?            -- it failed the vacuity check
    pub det out asked?

    req asked: asked? iff (consistent_q != Unsat and not vacuous?)
}
```

`check::non_redundancy` gives the verdict, from the outcome `q` of the
query:

```fren
pub comp non_redundancy {
    in q: Outcome          -- can the constraint be proved from the others?
    pub det out verdict: Verdict

    req independent: when q = Sat, verdict = Pass
    req redundant: when q = Unsat, verdict = Fail
    req unknown: when q = Unknown, verdict = Inconclusive
}
```

## Definedness

An index `q[i]` is unspecified unless `0 <= i < q.len` (see
[Expressions](Lang/Expressions.md#sequences)): the checks hold for every
value it could have, so an out-of-range index is sound, but the constraint
then says nothing useful there, which is almost always a mistake. For each
index in a constraint, a definition or a binding, with its guard `G`, Fren
asks whether `0 <= i and i < q.len` can be proved from `G` and the
hypotheses of where it is written:

| Where | Hypotheses |
|---|---|
| an assumption | the other assumptions |
| a requirement, expectation or definition | `A`, `I` and `R`, as for vacuity |
| a binding of an instance | `A`, and the instances declared before it |
| a global expectation | the meanings of its binders' components |

A requirement's own `R` is among its hypotheses, so a requirement can
guarantee its own definedness through another, such as `req long: q.len >
3` beside `req third: q[3] = x`: the system meets both or neither. A
component with no index has no definedness results. `check::definedness`
decides each query like an expectation, and a model is a counterexample,
reported at the `[` of the index:

```fren
pub comp definedness {
    in q: Outcome          -- can `0 <= i < q.len` be proved from the guard and the hypotheses?
    pub det out verdict: Verdict
    pub det out reports_cex?

    inst as_expect: expectation { q }

    req like_expect: verdict = as_expect.verdict and (reports_cex? iff as_expect.reports_cex?)
}
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

    req rule: minimal? iff (core subset candidates and refutes?(core)
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
inputs, as in `req r: x = f(i)`, is determined. `check::copied` gives what
the second copy renames:

```fren
pub enum Symbol { Input, InstanceVariable, Output, Function }

pub comp copied {
    in symbol: Symbol
    pub det out copied?

    req rule: copied? iff (symbol = Symbol::InstanceVariable or symbol = Symbol::Output)

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

    req like_expect: verdict = as_expect.verdict and (reports_cex? iff as_expect.reports_cex?)
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
| an expectation | the expectation, its vacuity and its definedness |
| an instance | the instance's assumptions, and the definedness of its bindings |
| a `det out` | its determinism |
| a component | all of the component's checks |
| a global expectation | its expectation, its vacuity and its definedness |
| a [refinement](Lang/Refinement.md) | all of the checks of its obligation, including the definedness of the bindings of the abstract component's instances |

As with a [lint setting](Lint.md), `set_option` without `in` sets the
evidence of every later component, global expectation and
[refinement](Lang/Refinement.md) in the file, and
before any other item it sets nothing. Within a component, the setting must
be followed by `in` and by a member whose checks it sets: before anything
else, such as a requirement, it is an error (`F0215`), and so is a
`set_option` of any other option before a member (`F0216`). The setting is a
statement that the solver cannot be relied on there, so it is never
reported as unneeded. A value other than `"tested"` or `"solver"` is an
error (`F0214`) where it would set a check.

`fren check` asks the solver nothing about a check whose evidence is
testing. It tests the check with `--tests` tests (default 100) from
`--seed` (default 0), and reports the result as `fren quickcheck` does
(`eval::test_verdict`): a counterexample fails the check, and testing that
reaches no conclusion leaves it inconclusive, with the same warnings. The
checks that testing cannot decide are not run: vacuity and redundancy,
which ask whether something can hold at all, which a failed search does
not refute, and definedness, since an index out of range has no value
that the evaluator knows (see [Evaluation](Eval.md#searching-for-behaviours)),
so testing can neither pass nor fail it. A test that reaches
an expectation shows that its trigger can hold, which is what its vacuity
check would show. The summary counts the passes that came from testing:

```text
fren: 30 passed (2 by testing), 0 failed, 0 inconclusive, 0 redundant
```

Lean has no evaluator, so `#fren_check` does not run a check whose evidence
is testing: it reports, as information, that `fren check` tests it. Such a
check is not part of the [agreement with Lean](Cli.md#agreement-with-lean).

`check::by_testing` gives how a check is run:

```fren
pub enum Run { BySolver, ByTesting, NotRun }

pub comp by_testing {
    use self::Kind::{Definedness, Redundancy, Vacuity}
    use self::Run::{BySolver, ByTesting, NotRun}
    in kind: Kind
    in tested?             -- the check's evidence is testing
    pub det out run: Run

    req solver: unless tested?, run = BySolver
    req testable: when tested? and not kind in {Vacuity, Redundancy, Definedness}, run = ByTesting
    req untestable: when tested? and kind in {Vacuity, Redundancy, Definedness}, run = NotRun

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
refine determinism_proves: determinism refines proved
refine vacuity_witnesses: non_vacuity refines satisfiable
refine redundancy_witnesses: non_redundancy refines satisfiable

#fren_check
```
