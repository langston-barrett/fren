# Checks

Fren checks each procedure seven ways:

| Check | Reported as | Confirms |
|---|---|---|
| [Realizability](#realizability) | `realizable` | some system can meet the guarantees, for every admissible input |
| [Expectations](#expectations) | `expect` | each expectation follows from the assumptions and guarantees |
| [Cover goals](#cover-goals) | `cover` | some behaviour that meets the assumptions and guarantees satisfies each cover goal |
| [Call assumptions](#call-assumptions) | `instance` | each call's arguments satisfy the called procedure's assumptions |
| [Vacuity](#vacuity) | `vacuity` | the trigger of each guarantee and expectation can hold |
| [Redundancy](#redundancy) | `redundancy` | no assumption or guarantee follows from the others |
| [Determinism](#determinism) | `determinism` | each `det` output is determined by the inputs |

and checks how its constraints are written six more ways, wherever they
have an index, a [table](Lang/Expressions.md#tables), a
[`match`](Lang/Expressions.md#matches) with guards, an application of a
function with a [contract](Lang/Items.md#contracts), or a value given
where a [subset type](Lang/SubsetTypes.md) is declared:

| Check | Confirms |
|---|---|
| [Definedness](#definedness) | each index is in range where it is evaluated |
| [Subset types](#pattern-types) | each value given where a pattern type is declared matches its pattern |
| [Completeness](#completeness) | some row of each table without a `_` row holds, and some arm of each `match` that needs its guards to be exhaustive is taken, where it is evaluated |
| [Disjointness](#disjointness) | no two rows of a table, other than `_`, hold at once, and no two arms of a [table over a scrutinee](Lang/Expressions.md#tables-over-a-scrutinee) are taken at once, where it is evaluated |
| [Preconditions](#preconditions) | each application of a function meets the function's preconditions where it is evaluated |
| [Reachability](#reachability) | each arm of a `match` that has a guard or follows one, and each row of a table, can be taken where it is evaluated |

A [global expectation](Lang/Global.md) is checked five of the first seven
ways, as a procedure is: the realizability check confirms that its
assumptions can hold, and the others its [expectations](#global-expectations),
its cover goals, its calls' assumptions, and the vacuity of its
expectations.
The body of a
[defined function](Lang/Items.md#defined-functions), the value of a
[constant](Lang/Items.md#constants), and the clauses of a function's
[contract](Lang/Items.md#contracts) are checked for completeness,
disjointness, reachability and preconditions too, a defined function's
[postconditions](#postconditions) are checked to hold, and the values in a
body or a value given where pattern types are declared, including the body
or value itself, are checked for their patterns.

The formulas below use the notation of [Procedures](Lang/Procedures.md#meaning):
`A` is the conjunction of the procedure's assumptions, `R` of its
guarantees, and `I` of its calls, over the inputs `i`, the calls'
variables `y` and the outputs `o`.
`D` is the equations `d = e` of the procedure's
[definitions](Lang/Procedures.md#definitions), and `o` excludes the
variables they define.
`N` is the constraints that [natural
numbers](Lang/Procedures.md#natural-numbers), [subset
types](Lang/Procedures.md#pattern-types) and the
[postconditions](Lang/Items.md#contracts) of uninterpreted functions
bring: `N(i, y)` that each `Nat` input and call variable, and each
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
formulas: a call's query has none about its procedure's
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
[interpretation](Lang/Procedures.md#interpretations), and a model gives an
interpretation as well as values for the variables. Hence:

- Realizability, expectations, call assumptions and determinism pass
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
pub proc proved(
    q: Outcome,            -- can the goal be proved?
): (det verdict: Verdict) {
    ensure proof: verdict = Pass iff q = Unsat
    ensure counterexample: verdict = Fail iff q = Sat

    expect conservative: when q = Unknown, verdict = Inconclusive
}

set_option fren.evidence "enumerated" in
pub proc satisfiable(
    q: Outcome,            -- can the negation of the goal be proved?
): (det verdict: Verdict) {
    ensure witness: verdict = Pass iff q = Sat
    ensure refuted: verdict = Fail iff q = Unsat

    expect conservative: when q = Unknown, verdict = Inconclusive
}
```

`check::applies` gives which checks run on an item. A global expectation
constrains nothing, so there is nothing to determine or find redundant:
it has no outputs, no guarantees and no `det` members, and its assumptions
say what it is about rather than constrain a system. With no outputs, its
realizability is only that its assumptions are satisfiable, which is still
asked, since contradictory assumptions would make every expectation hold
vacuously. Its calls' arguments have obligations, as a procedure's do. A
global expectation in the [short form](Lang/Global.md#the-short-form),
`ShortExpectation`, has no assumptions, so it is not asked that either. The body of a
function, its contract, or the value of a constant is not a constraint
either: only its tables, its `match`es with guards, the applications in
it, and its values given where pattern types are declared are checked, and
the function's postconditions. The [pattern-type check](#pattern-types) is
part of definedness: its results are definedness results, and it runs
where definedness does, though in a body or a value, definedness asks
nothing of its indexes. A procedure has no postconditions, so their check
has no results there. The contract of an uninterpreted function with
postconditions is checked for [realizability](#realizability) too, as a
procedure whose parameters are the function's parameters, whose one `det`
result is its value, and whose assumptions and guarantees are its preconditions
and postconditions (see [Contracts](#contracts-of-uninterpreted-functions)):

```fren
pub enum CheckedItem { Component, GlobalExpectation, ShortExpectation, Body, Contract }

set_option fren.evidence "enumerated" in
pub proc applies(item: CheckedItem, kind: Kind): (det runs?) {
    use self::CheckedItem::{Body, Component, Contract, GlobalExpectation, ShortExpectation}
    use self::Kind::{
        Completeness,
        Cover,
        Definedness,
        Determinism,
        Disjointness,
        Expectation,
        InstanceAssumption,
        Postcondition,
        Precondition,
        Reachability,
        Realizability,
        Redundancy,
        Vacuity,
    }

    ensure rule: runs? iff match item {
        Component => true,
        GlobalExpectation => kind in {Realizability, InstanceAssumption, Expectation, Cover, Vacuity, Definedness,
            Completeness, Disjointness, Precondition, Reachability},
        ShortExpectation => kind in {InstanceAssumption, Expectation, Cover, Vacuity, Definedness, Completeness,
            Disjointness, Precondition, Reachability},
        Body => kind in {Definedness, Completeness, Disjointness, Precondition, Postcondition, Reachability},
        Contract => kind in {Realizability, Completeness, Disjointness, Precondition, Reachability},
    }

    expect claims_only: when item in {GlobalExpectation, ShortExpectation, Body} and runs?,
        not kind in {Determinism, Redundancy}
    expect assumptions_satisfiable: when item = GlobalExpectation and kind = Realizability, runs?
    expect determined: when item != Component, kind != Determinism or not runs?
}
```

## Realizability

A procedure is realizable if some system can respond to every admissible
input, whatever its calls do:

  ∀ i y. A(i) ∧ I(i, y) ⇒ ∃ o. R(i, y, o)

with each variable that has a definition replaced by it (see
[Definitions](#definitions)), and `N(o)` a conjunct of `R`, so that the
outputs that `∃` ranges over are `Nat`s where their types say so.

Fren asks two queries:

- **Assumptions.** Can `False` be proved from `A`? If so, the assumptions
  are contradictory, so the formula above holds vacuously, and the check
  fails rather than passing. Fren reports a minimal set of contradictory
  assumptions.
- **Counterexample.** Can `∃ o. R(i, y, o)` be proved from `A` and `I`, with
  the inputs and call variables free? A model is an input, together
  with a behaviour of the calls, that no system could answer. Fren
  reports it, with a [minimal](#minimal-sets) set of guarantees that
  conflict on it, its *core*, and notes at the guarantees of the core that
  force an output to a value that the rest of the core rules out (see
  [Forced outputs](#forced-outputs)).

`check::realizability` gives the verdict and what is reported, from the
outcomes of the two queries (`assume_q` and `cex_q`). Its table's rows
cover the nine pairs of outcomes, each exactly once, which the
[completeness](#completeness) and [disjointness](#disjointness) checks
confirm:

```fren
set_option fren.evidence "enumerated" in
pub proc realizability(
    assume_q: Outcome,     -- can `False` be proved from A?
    cex_q: Outcome,        -- can `exists outputs, R` be proved from A and I?
): (
    det verdict: Verdict,
    det reports_cex?,          -- report the input and the conflicting guarantees
    det reports_vacuous?,         -- report that the assumptions are contradictory
) {
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

Recursive defined functions reuse these application facts and argument
obligations. Their contracts are checked against their bodies by Hoare
induction, as [Recursion](Lang/Recursion.md#contracts) specifies, rather
than by contract realizability. Their counterexamples require confirmation
by evaluation; a refuted model yields Inconclusive (`F0450`).

An uninterpreted function's [postconditions](Lang/Items.md#contracts)
are assumed at each of its applications, so if they cannot hold together,
every check that applies the function holds vacuously. So its contract is
checked as a procedure is: the inputs are its parameters `x`, the one
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
of a procedure, and so are the verdicts, but the failures are reported at
the function's name: contradictory preconditions (`F0632`), and arguments
for which no value meets the postconditions (`F0631`), with a minimal set
of postconditions that conflicts on them, and notes at those that force
the value to one that the others rule out (see [Forced
outputs](#forced-outputs)).

`check::contract_realizability` states the verdict, over a small domain:
two arguments and two values, where the preconditions hold at the
arguments `pres`, and the postconditions at the pairs `posts`. Where no
argument meets the preconditions, they contradict each other, and the
check fails. Its
implementation builds the contract's procedure as both front ends do,
and runs the realizability check on it, with a solver that decides by
trying every argument and value:

```fren
pub enum Argument { A0, A1 }
pub enum Value { V0, V1 }
pub struct Point { arg: Argument, value: Value }

pub proc contract_realizability(
    pres: Set<Argument>,     -- the arguments that meet the preconditions
    posts: Set<Point>,       -- the arguments and values that meet the postconditions
): (
    det verdict: Verdict,
    det reports_cex?,              -- report the arguments and the conflicting postconditions
    det reports_vacuous?,          -- report that the preconditions are contradictory
) {
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

It refines `check::realizability`, the check of a procedure, whose
queries' answers are those of the contract over this domain: the
preconditions are contradictory exactly when no argument meets them, and
the postconditions can be proved satisfiable exactly when every argument
that meets the preconditions has a value that meets the postconditions:

```fren
expect contract_realizes(pres: Set<check::Argument>, posts: Set<check::Point>) {
    use check
    call concrete := contract_realizability(pres, posts)
    refines concrete realizability(if (pres) = {} then check::Outcome::Unsat else check::Outcome::Sat, if forall (a: check::Argument), when (a) in (pres), exists (v: check::Value), check::Point { arg := (a), value := (v) } in (posts)
            then check::Outcome::Unsat else check::Outcome::Sat)
}
```

### Query order

The counterexample query is asked only when the assumptions query does not
return `Unsat`; otherwise its outcome is taken to be `Unknown`.
`check::realizability_protocol` confirms that this gives the same verdict
and reports as always asking both. `always` is the check with the solver's
answer to `cex_q`, and `asked` the check as Fren runs it:

```fren
expect realizability_protocol(
    asked_assume_q: Outcome,
    asked_cex_q: Outcome,
    always_assume_q: Outcome,
    always_cex_q: Outcome,
) {
    call asked := realizability(asked_assume_q, asked_cex_q)
    call always := realizability(always_assume_q, always_cex_q)
    expect realizability_protocol: when asked.assume_q = always.assume_q
        and asked.cex_q = (if always.assume_q = Unsat then Unknown else always.cex_q),
        asked.verdict = always.verdict
        and (asked.reports_cex? iff always.reports_cex?)
        and (asked.reports_vacuous? iff always.reports_vacuous?)
}
```

### Forced outputs

The primary conflict reports one counterexample input and its minimal core.
Additional forcing notes have a different scope: they must hold for every
model of the procedure's assumptions, definitions and calls, together
with the named guarantees. Input pins from the primary counterexample
are not premises of these explanations. Each side must admit a model;
otherwise it cannot be described as forcing an output.

For example, unconditional guarantees requiring an output to be true
and false can be explained by the plain sentence:

```text
note: `enable` requires `retry?` to equal true, while `disable` requires it to equal false.
```

An output whose type is an
[enumeration](Lang/Items.md#enumerations), [generic](Lang/Generics.md) or
not, may be forced only part of the way: a set of guarantees *forces* the output to a *variant* when every
assignment that satisfies them gives the output a value of that variant,
whatever its payload. A side that rules out `Decision::GiveUp` forces
`Decision::RetryAfter`, without forcing a delay. Where the two sides force
values of different variants, the note says what each forces, a whole
value where it forces one, and otherwise the variant, as the pattern test
that holds of every value of it:

```text
note: `must_retry` requires `decision` to match Decision::RetryAfter(_), while `must_stop` requires it to equal Decision::GiveUp.
```

The outputs are the procedure's results that have no
[definition](#definitions): a result that has one is replaced by its
definition, so what forces it forces the outputs that it is defined by. For an
uninterpreted function's [contract](#contracts-of-uninterpreted-functions),
the one output is its value. Let `B` be the general assumptions and call
facts, with definitions substituted. The primary core may have been found
with a pinned input, but these explanation queries do not use that pin.
For a set of guarantees `S`, Fren asks:

- **Model.** Can `False` be proved from `B` and `S`? A `Sat` answer proves
  that the context is nonempty and supplies candidate output values. Neither
  `Unsat` nor `Unknown` establishes a forcing fact for a diagnostic.
- **Pin.** For an output `o` and its value `v` in the model, can `o = v` be
  proved from `B` and `S`? `Unsat` means that `S` forces `o` to `v`.
- **Variant.** For an output `o` of an enumeration and its value `v` in
  the model, of the variant `C`, can `o is C(_)` be proved from `B` and
  `S`, with a `_` for each value of `C`'s payload? `Unsat` means that `S`
  forces `o` to `C`. A [newtype](Lang/Items.md#newtypes) of an
  enumeration is not asked about: no pattern matches its values, so a
  note could not say what is forced as a pattern test of the output.

`check::forcing` states that the queries find what forcing means, over
an output with three values of two variants, `C0` and `C1(b)`: `values`
are its values in the assignments that satisfy `B` and `S`, the
model's is one of them, and the solver decides the pin and variant
queries. A value that cannot be written in a formula is not pinned, and
so not found to be forced, nor is a variant of a type that is not an
enumeration:

```fren
pub enum Choice { C0, C1(Bool) }

-- The variants of `Choice`.
pub enum ChoiceVariant { K0, K1 }

pub fn variant_of(c: Choice): ChoiceVariant := match c {
    Choice::C0 => ChoiceVariant::K0,
    Choice::C1(_) => ChoiceVariant::K1,
}

pub proc forcing(
    values: Set<Choice>,     -- the output's values where `B` and `S` hold
    model: Choice,           -- its value in the model of `B` and `S`
    pin_q: Outcome,          -- can `o = model` be proved from `B` and `S`?
    variant_q: Outcome,      -- can `o` being of `model`'s variant be proved from `B` and `S`?
): (
    det forced?,                  -- `S` forces the output under the premises
    det found?,                   -- Fren finds that `S` forces it to `model`
    det variant_forced?,          -- `S` forces the output to a variant under the premises
    det variant_found?,           -- Fren finds that `S` forces it to `model`'s variant
) {
    assume modelled: model in values
    assume decided: pin_q = (if (forall (v: Choice), when v in values, v = model) then Unsat else Sat)
    assume variant_decided:
        variant_q = (if (forall (v: Choice), when v in values, variant_of(v) = variant_of(model)) then Unsat else Sat)

    ensure meaning: forced? iff (forall (a b: Choice), when a in values and b in values, a = b)
    ensure query: found? iff pin_q = Unsat
    ensure variant_meaning:
        variant_forced? iff (forall (a b: Choice), when a in values and b in values, variant_of(a) = variant_of(b))
    ensure variant_query: variant_found? iff variant_q = Unsat

    expect computes: found? iff forced?
    expect variant_computes: variant_found? iff variant_forced?
    expect value_then_variant: when forced?, variant_forced?
}
```

For each guarantee `E` of the core, in the core's order, Fren asks the
model query of `{E}` and of the rest of the core, and then, for each
output in the order of the procedure's variables whose values in the two
models differ, what each side forces of it: the pin query of `{E}` and,
if it forces the output, of the rest. Where the two values are of
different variants, a side that does not force the output's value is
asked the variant query too, and forces its variant if the answer is
`Unsat`; the rest is asked only if `{E}` forces something. The clash note is at
the first output where the two sides force different values, or values
of different variants: a whole value where a side forces one, and its
variant otherwise. So a clash of whole values is preferred, and two
sides that force only the same variant do not clash. Outputs whose values in the
models are the same are not asked about, since two sets that force an
output give it their forced values in their models, and those that force
its variant give it a value of that variant. When the core has one
guarantee, its rest is empty and forces nothing, so no clash note is asked
for. Fren shows at most `examples` clash notes, `--examples` or
the Lean-hosted front end's `fren.examples` (see [Forced
outputs](Cli.md#forced-outputs)), and asks no more of these queries once
it has them all.

A note's values would depend on an
[interpretation](Lang/Procedures.md#interpretations) where some variable
of the procedure, its own or a call's, has a type that is or contains
an [abstract type](Lang/Types.md#abstract-types), or where a guarantee or
a definition substituted into one uses an abstract type or an
[uninterpreted function](Lang/Items.md#uninterpreted-functions), directly
or through a defined function. A model then fixes an interpretation that
the note could not show, so a failure has no notes there, and none of
their queries are asked, as for the witness of a [cover
goal](View.md#check-results). Both front ends decide this by the same rule.

Every guarantee of the core has one note, so that an editor marks each:
its clash note, if it has one; else, that it conflicts with the rest of
the core; or, in a core of one, that it is false for the input. The input
itself is in the error's note, so these do not repeat it (see [Check
results](View.md#check-results)).

`check::clash_notes` states which guarantees have a clash note, and which
note each has, over a core of
at most three guarantees, in the order of the enumeration, and two
outputs, in the order of theirs, each of type `Choice`. `alone` and
`alone_variants` hold what each guarantee `g` forces on its own, values
and variants, and `rest` and `rest_variants` what the rest of the core
forces, as the queries above find them: a set that forces a value forces
its variant too, so a clash of whole values or of variants is a clash of
what the note shows, a whole value where the side forces one; `earlier` is the guarantees of
the core before `g` that have a clash. The rules are of the guarantee
`g`, so quantifying over it states them of the whole core:

```fren
pub ordered enum Guarantee { G0, G1, G2 }
pub ordered enum Output { O0, O1 }

-- A set of guarantees forces `output` to `value`; `guarantee` is the one
-- that it is, or that it is the rest of.
pub struct Forcing { guarantee: Guarantee, output: Output, value: Choice }

-- A set of guarantees forces `output` to a value of `variant`.
pub struct VariantForcing { guarantee: Guarantee, output: Output, variant: ChoiceVariant }

pub enum Budget { All, AtMost(Int) }   -- `all`, or a count, at least 0

-- A note is emitted only for an additional proved general relationship.
pub enum MemberNote { ClashNote, Silent, NotInCore }

-- `g` forces `o` to one value, and the rest of the core to another.
pub fn value_clashes?(alone: Set<Forcing>, rest: Set<Forcing>, g: Guarantee, o: Output) :=
    exists (a b: Choice), a != b and Forcing { guarantee := g, output := o, value := a } in alone
    and Forcing { guarantee := g, output := o, value := b } in rest

-- `g` forces `o` to one variant, and the rest of the core to another.
pub fn variant_clashes?(alone: Set<VariantForcing>, rest: Set<VariantForcing>, g: Guarantee, o: Output) :=
    exists (k l: ChoiceVariant), k != l and VariantForcing { guarantee := g, output := o, variant := k } in alone
    and VariantForcing { guarantee := g, output := o, variant := l } in rest

-- `g` forces `o` to one value or variant, and the rest of the core to another.
pub fn clashes?(alone: Set<Forcing>, alone_variants: Set<VariantForcing>, rest: Set<Forcing>,
    rest_variants: Set<VariantForcing>, g: Guarantee, o: Output) :=
    value_clashes?(alone, rest, g, o) or variant_clashes?(alone_variants, rest_variants, g, o)

-- A set of guarantees forces `o` to a whole value, for the guarantee `g`.
pub fn forces_value?(forced: Set<Forcing>, g: Guarantee, o: Output) :=
    exists (v: Choice), Forcing { guarantee := g, output := o, value := v } in forced

-- A set of guarantees forces each output to one value, at most.
pub fn single_valued?(forced: Set<Forcing>) :=
    forall (h: Guarantee) (o: Output) (a b: Choice),
    when Forcing { guarantee := h, output := o, value := a } in forced
    and Forcing { guarantee := h, output := o, value := b } in forced, a = b

-- A set of guarantees forces each output to one variant, at most, and to
-- the variant of each value that it forces it to.
pub fn variants_of?(forced: Set<Forcing>, variants: Set<VariantForcing>) :=
    (forall (h: Guarantee) (o: Output) (k l: ChoiceVariant),
    when VariantForcing { guarantee := h, output := o, variant := k } in variants
    and VariantForcing { guarantee := h, output := o, variant := l } in variants, k = l)
    and (forall (h: Guarantee) (o: Output) (v: Choice), when Forcing { guarantee := h, output := o, value := v } in forced,
    VariantForcing { guarantee := h, output := o, variant := variant_of(v) } in variants)

pub proc clash_notes(
    core: Set<Guarantee>,
    alone: Set<Forcing>,                     -- the values that each guarantee forces on its own
    alone_variants: Set<VariantForcing>,     -- the variants that each guarantee forces on its own
    rest: Set<Forcing>,                      -- the values that the rest of the core forces, for each guarantee
    rest_variants: Set<VariantForcing>,      -- the variants that the rest of the core forces
    examples: Budget,                        -- `--examples`
    interpreted?,                            -- the notes' values would depend on an interpretation
    consistent?,                             -- the general forcing contexts have models
    g: Guarantee,                            -- a guarantee, for the rules of each
    earlier: Set<Guarantee>,
): (
    det noted?,                -- a clash note is at `g`
    output: Output,            -- the output that it names
    shows_value?,
    rest_shows_value?,
    det note: MemberNote,
) {
    -- What the queries find of the guarantees of the core: one value and
    -- one variant, at most, for each output, and nothing of the empty rest
    -- of a core of one.
    assume of_core: forall (f: VariantForcing), when f in alone_variants or f in rest_variants, f.guarantee in core
    assume one_value: single_valued?(alone) and single_valued?(rest)
    assume one_variant: variants_of?(alone, alone_variants) and variants_of?(rest, rest_variants)
    assume empty_rest: forall (f: VariantForcing), when f in rest_variants, core != {f.guarantee}
    assume earlier_clashes: forall (h: Guarantee),
        h in earlier iff (h in core and h < g
        and (exists (o: Output), clashes?(alone, alone_variants, rest, rest_variants, h, o)))
    -- The note gives what `g` forces of `output` as a whole value, not a
    -- variant, where it forces one, and so of what the rest of the core forces.
    out shows_value? := forces_value?(alone, g, output)
    out rest_shows_value? := forces_value?(rest, g, output)

    ensure rule: noted? iff (not interpreted? and consistent? and g in core
        and (exists (o: Output), clashes?(alone, alone_variants, rest, rest_variants, g, o))
        and match examples { Budget::All => true, Budget::AtMost(n) => earlier.card < n })
    ensure first: when noted?, clashes?(alone, alone_variants, rest, rest_variants, g, output)
        and (forall (o: Output), when o < output, not clashes?(alone, alone_variants, rest, rest_variants, g, o))
    ensure one_note: note = (if not (g in core) then MemberNote::NotInCore
        else if noted? then MemberNote::ClashNote
        else MemberNote::Silent)

    expect single: when core = {g}, not noted?
    expect none: when examples = Budget::AtMost(0), not noted?
    expect uninterpreted: when interpreted?, not noted?
    expect nonvacuous: when not consistent?, not noted?
    expect marked: when g in core, note != MemberNote::NotInCore
    expect no_repeated_core: when g in core and not noted?, note = MemberNote::Silent
    expect within_budget: when noted? and examples = Budget::AtMost(1), earlier = {}
    expect variants_differ: when noted? and not (shows_value? and rest_shows_value?),
        variant_clashes?(alone_variants, rest_variants, g, output)
}
```


### Conditional branch cores

[Named Boolean blocks](Lang/BooleanBlocks.md#branch-conflict-explanations)
retain their owning constraint in the unconditional minimal core. Branch
explanations are conditional: one alternative replaces that owner while
its other core constraints are minimized. An alternative carries its
source member name and the original leading guards. The replacement is
never presented as the unconditional core of the original disjunction.
For equivalence the alternatives are exactly the conjunction of positive
members and the conjunction of negative members, including binary `iff`.

Supplementary explanations state properties that hold in every model of
explicit, consistent premises. They are not evaluations of a selected
counterexample. Keep the primary counterexample and its input-local
minimal core, but do not reuse its input pins to justify any supplementary
forced value, operand polarity, or branch elimination. A generic repeated
“conflicts with” note is not a substitute for an additional proved property.
If no additional general property is proved, emit no supplementary note.
An empty collection of alternatives is not by itself a proof that a
guarded owner is impossible; do not emit a vacuous all-branches heading.

For realizability, the general base consists of the procedure's assumptions
and call facts, with definitions substituted just as in the primary query.
The other premises are named core constraints. Remove a source group's
own constraint from the base before inspecting its alternatives, including
when it is itself an assumption. Do not add unlisted remaining guarantees
to the base: the complete inconsistent specification is never a premise. For a
failed cover or a vacuous trigger, the cover goal or trigger may be an
explicit conditional premise, together with the definitions and applicable
assumptions/calls. Name that condition in the explanation; it is not an
input pin. Those contexts also exclude the selected owner; their other
premises must be stated, not silently inherited from the full specification.
For conflicting assumptions, inspect the selected assumption
against the others, without assuming the inconsistent complete set.

Before excluding an alternative, require a model of the base and the
other named premises. Only then can an unsatisfiability proof with the
alternative establish its impossibility in all models of those premises.
Each side used for a forcing comparison must itself have a model. A
premise set with no model proves no forcing fact for diagnostics. Unknown
answers establish nothing and produce no claim. An inexact bounded
enumeration can still provide its primary counterexample or witness, but
cannot establish an unqualified all-model relationship; omit these
supplementary relationships unless its whole model space was exhausted.
These queries share the
same interpretation and use no value chosen from a counterexample as an
assumption. Only owners in the primary minimized core are inspected, and
the examples limit still counts groups. A selected group adds one shared
consistency query before its alternative query families; a zero limit or
an out-of-core group adds no queries.

Write the proved relationship as a plain sentence with its source names,
not a quoted `case "..."` heading or a transcript of Boolean evaluation.
For example: “Both operands of `transient` cannot be true: `honor_server`
and `latency_budget` require `transient.1` to be false.” If both alternatives
are possible for some admitted inputs, omit both notes even when one is
impossible at the particular counterexample. Do not claim that an impossible
alternative forces arbitrary outputs. Preserve source ranges, occurrence
identities, the original core, and the primary verdict. Model observations
attached to a counterexample or cover witness remain explicitly local
observations; they are not general implications.

The following model uses actual candidate worlds, each with two input
properties and an output decision. `base` and `others` denote premises;
a local input slice cannot certify a general branch exclusion.

```fren
pub struct DiagnosticWorld { eligible?, within_budget?, retry? }

pub proc general_branch_explanation(base: Set<DiagnosticWorld>, others: Set<DiagnosticWorld>,
    alternative: Set<DiagnosticWorld>, sample: DiagnosticWorld,
    context_q: Outcome, exclusion_q: Outcome): (
    det consistent?, det excluded?, det reported?, det locally_excluded?,
) {
    assume context_sound: when context_q != Unknown,
        (context_q = Sat iff base inter others != {})
    assume exclusion_sound: when exclusion_q != Unknown,
        (exclusion_q = Unsat iff base inter others inter alternative = {})
    out reported? := context_q = Sat and exclusion_q = Unsat
    out consistent? := base inter others != {}
    out excluded? := consistent? and base inter others inter alternative = {}
    out locally_excluded? := not (exists (w: DiagnosticWorld),
        w in base inter others inter alternative and w.eligible? = sample.eligible?
        and w.within_budget? = sample.within_budget?)
    expect reported_sound: when reported?, excluded?
    expect unknown_silent: when context_q = Unknown or exclusion_q = Unknown, not reported?
    expect all_models: when excluded?, forall (w: DiagnosticWorld),
        when w in base inter others, not w in alternative
    expect nonvacuous: when base inter others = {}, not excluded?
    cover local_is_insufficient: consistent? and sample in base inter others
        and locally_excluded? and not excluded?
}

pub proc retry_alternatives_general(worlds: Set<DiagnosticWorld>): (det true_possible?, det false_possible?, det bad_input?) {
    assume all_worlds: forall (w: DiagnosticWorld), w in worlds
    out true_possible? := exists (w: DiagnosticWorld), w in worlds and w.retry? and w.eligible?
        and (when w.retry?, w.within_budget?)
    out false_possible? := exists (w: DiagnosticWorld), w in worlds and not w.retry? and not w.eligible?
        and (when w.retry?, w.within_budget?)
    out bad_input? := not (exists (w: DiagnosticWorld), w in worlds and w.eligible? and not w.within_budget?
        and (w.retry? iff w.eligible?) and (when w.retry?, w.within_budget?))
    expect both_globally_possible: true_possible? and false_possible?
    expect still_a_counterexample: bad_input?
}
```

The following finite interpretation defines deletion-minimal conditional
cores using actual assignments (`Choice`) and a relation giving each
candidate constraint's satisfying assignments. `base` contains the explicitly stated general premises and definitions,
never counterexample input pins. An impossible branch can have an empty
conditional core; that does not let the forcing queries invent a value.

```fren
pub fn branch_rest_holds?(meaning: Rel<Guarantee, Choice>, selected: Set<Guarantee>, value: Choice) :=
    forall (g: Guarantee), when g in selected, (g, value) in meaning

pub proc conditional_branch_core(
    branch: Set<Choice>,
    base: Set<Choice>,
    meaning: Rel<Guarantee, Choice>,
    candidates: Set<Guarantee>,
    conditional: Set<Guarantee>,
): (valid?, minimal?) {
    ensure refutes: valid? iff conditional subset candidates and
        not (exists (v: Choice), v in branch and v in base and branch_rest_holds?(meaning, conditional, v))
    ensure deletion_minimal: minimal? iff valid? and
        (forall (g: Guarantee), when g in conditional,
        exists (v: Choice), v in branch and v in base and branch_rest_holds?(meaning, conditional minus {g}, v))
    expect within: when valid?, conditional subset candidates
    expect impossible_empty: when branch inter base = {} and conditional = {}, valid? and minimal?
    expect no_fake_global_core: when conditional = {} and branch = {} and base != {}, minimal?
}

pub proc branch_member_polarity(rest: Set<Choice>, positive_values: Set<Choice>, wanted?): (opposite_forced?) {
    ensure nonvacuous_opposite: opposite_forced? iff rest != {} and
        (forall (v: Choice), when v in rest, (v in positive_values) iff not wanted?)
    expect positive_blocked: when wanted?, opposite_forced? iff rest != {} and rest inter positive_values = {}
    expect negative_blocked: when not wanted?, opposite_forced? iff rest != {} and rest subset positive_values
    expect no_vacuous_forcing: when rest = {}, not opposite_forced?
}
```

A member-polarity note is made only after the rest has a model. For the
all-hold equivalence branch, each member is asked positively; for the
none-hold branch, negatively. A successful opposite-polarity proof is
minimized against the other core constraints, retaining the branch and
member identity in the result. Unknown answers never produce a forcing
claim. A branch with no satisfying assignment is described as impossible
rather than as forcing every value. Whole-value and variant clashes use
exactly the existing non-vacuous model/pin/variant protocol.

Only groups whose owners occur in the already minimized core are
inspected. Realizability explanations use substituted definitions and general
assumptions/calls, without the primary core's input pins. Vacuity explanations use the check's
definition equations and the triggering condition (or the failed cover
goal) as fixed hypotheses.
Unsatisfiable procedure assumptions use their minimal assumption core.
Unrelated groups cost no branch queries. The examples limit counts groups,
so selecting an equivalence group retains both of its alternatives; a
zero limit asks no branch queries. Conditional minimization is additional
explanatory work and cannot change the primary verdict or its original
minimal core. Each source member retains its original text and range.

## Definitions

A definition, of a result or a `let` variable, is not a constraint, and
the checks never search for the value of the variable it defines.
Realizability replaces each such variable by its definition, so that the
`∃` ranges over the other outputs only, whose types are bounded. Every
other check adds `D` to its hypotheses, as equations, so each defined
variable is a variable of the query and its value appears in models.
A definition is never a candidate for redundancy, nor reported in a
minimal set. `check::definitions` states the choice:

```fren
pub proc definitions(kind: Kind): (
    det substituted?,            -- replaced by their definitions, rather than assumed as equations
) {
    ensure rule: substituted? iff kind = Kind::Realizability

    expect never_searched: when kind = Kind::Realizability, substituted?
}
```

Both forms mean the same, since every definition determines its output.
Substituting everywhere would lose defined variables' values in models;
using the equations in realizability would put defined variables under `∃`.

## Expectations

For each expectation `e`, Fren asks whether `e` can be proved from `A`, `I`
and `R`. A model is a counterexample: Fren reports the values of the inputs
and results in it.

If `A ∧ I ∧ R` is unsatisfiable, every expectation passes vacuously. The
realizability check then fails for the same procedure.

`check::expectation` gives the verdict, from the outcome `q` of the query:

```fren
set_option fren.evidence "enumerated" in
pub proc expectation(
    q: Outcome,            -- can `e` be proved from A, I and R?
): (det verdict: Verdict, det reports_cex?) {
    ensure holds: when q = Unsat, verdict = Pass
    ensure refuted: when q = Sat, verdict = Fail
    ensure unknown: when q = Unknown, verdict = Inconclusive
    ensure report_cex: reports_cex? iff q = Sat
}
```

## Cover goals

A [cover goal](Lang/Procedures.md#cover-goals) `cover n: e` claims that
some behaviour meets the procedure and satisfies `e`: that

  A ∧ I ∧ R ∧ e

is satisfiable, with `D` among the hypotheses. Fren asks whether `not e`
can be proved from `A`, `I` and `R`. A model is a *witness*: a behaviour
that meets the procedure, in which the goal holds, and the goal passes.
If `not e` is proved, no behaviour meets the goal, and it fails
(`F0615`): Fren
reports a minimal set of assumptions and guarantees that rule it out,
as for [vacuity](#vacuity). If `A ∧ I ∧ R` is unsatisfiable, every cover
goal fails, with the realizability check.

So a cover goal is the converse of an expectation: an expectation holds if
its negation is impossible, a cover goal if it is possible. And the
vacuity check of a guarantee or expectation with the trigger `C` is the
cover goal `C`, with the same query. A cover goal is checked only in its
own procedure: a call of the procedure does not check it again.

`check::cover_goal` gives the verdict and what is reported, from the outcome
`q` of the query:

```fren
set_option fren.evidence "enumerated" in
pub proc cover_goal(
    q: Outcome,            -- can `not e` be proved from A, I and R?
): (
    det verdict: Verdict,
    det reports_witness?,         -- report the model, in which the goal holds
    det reports_core?,            -- report the constraints that rule the goal out
) {
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

A global expectation is checked as a procedure with its parameters as
inputs, its assumptions, its calls, its expectations and its cover goals,
and no outputs or guarantees (see [Global
expectations](Lang/Global.md#meaning)): `R` is empty, and `A` and `I` are
its own. For each expectation `E`, Fren asks whether `E` can be proved
from `A` and `I`; a model is a counterexample, in which Fren reports the
parameters and the calls' results, and `check::expectation` gives the
verdict. Its calls' assumptions are checked as a procedure's are, from
`A` and the earlier calls, and so are its cover goals and the vacuity of
its expectations' triggers. A global expectation in the short form,
`expect n: e`, is one with no parameters and no calls, whose `A` and `I`
are empty.

Its realizability check is a procedure's with no outputs: its
counterexample query proves `∃ o. R` at once, so it fails just where `A`
is unsatisfiable, with the procedure's message (`F0602`), naming the
assumptions that contradict each other. That `A ∧ I` is satisfiable
wherever `A` is follows from its other checks: each call's arguments meet
its procedure's assumptions, by the call checks, and the procedure is
realizable, by its own checks, so its constraints can hold.

That argument needs each called procedure's realizability to be proved.
Where it is not, because the procedure's realizability check is set to
testing ([evidence](#checking-by-testing)) or is inconclusive, the
procedure may have no outputs at some input that meets its assumptions.
At such an input `A ∧ I` is unsatisfiable, and the global expectation's
expectations pass there vacuously. With `assume a: x = 1234567`, `call c
:= tested_lies(x)` and `expect e: c.y = 0`, where `tested_lies` has no
outputs at `1234567`, `e` passes. Only the called procedure's own report
says so: its tested evidence, or its inconclusive result. So a global
expectation proves no more than its called procedures' realizability
does.

## Call assumptions

For each call `w` of a procedure `c`, and each assumption `a` of `c`,
and each parameter `x` of `c` whose type brings a constraint (see [Subset
types](Lang/Procedures.md#pattern-types)), before its assumptions,
Fren asks whether `a`, or `x`'s constraint, with `w`'s arguments substituted, can be proved from
`A`, the arguments of `w`, and the constraints `I_v` of the calls `v`
declared before `w`. A model is a counterexample: Fren reports the values of
the inputs, and of the results of the earlier calls.

`check::instance_assumption` decides each such query like an expectation:

```fren
pub proc instance_assumption(
    q: Outcome,            -- can it be proved from A, the arguments and earlier calls?
): (det verdict: Verdict, det reports_cex?) {
    call as_expect := expectation(q)

    ensure like_expect: verdict = as_expect.verdict and (reports_cex? iff as_expect.reports_cex?)

    expect never_upgrades: when q = Unknown, verdict != Pass
}
```

## Vacuity

A guarantee or expectation whose [trigger](Lang/Procedures.md#triggers)
can never hold is satisfied vacuously, which usually indicates a mistake.
For each guarantee and expectation with a trigger, Fren asks whether `not
trigger` can be proved from `A`, `I` and `R`, which are a global
expectation's own, its `R` empty. If it can, the check fails,
and Fren reports a minimal set of assumptions and guarantees that rule
the trigger out. Constraints without a trigger, and assumptions, are not
checked.

`check::non_vacuity` gives the verdict, from the outcome `q` of the query:

```fren
set_option fren.evidence "enumerated" in
pub proc non_vacuity(
    q: Outcome,            -- can `not trigger` be proved from A, I and R?
): (det verdict: Verdict) {
    ensure fires: when q = Sat, verdict = Pass
    ensure vacuous: when q = Unsat, verdict = Fail
    ensure unknown: when q = Unknown, verdict = Inconclusive
}
```

## Redundancy

An assumption or guarantee that follows from the procedure's other
constraints adds nothing to its meaning. If it is meant as a consequence,
it is better declared as an expectation, which the checks confirm rather
than take for granted.

For each assumption, Fren asks whether it can be proved from the other
assumptions. For each guarantee, Fren asks whether it can be proved from
`A`, `I` and the other guarantees. If it can, the check fails, and Fren
reports a minimal set of constraints it follows from. A redundant
constraint is not a mistake in itself, so the failure is a
[warning](View.md#severity), not an error.

An assumption is not compared with `I`, even though a called
procedure's assumptions, through the call's arguments, can constrain the
inputs: removing such an assumption would make the [call
check](#call-assumptions) fail.

Contradictory constraints entail everything, so the assumptions are not
checked if `A` is unsatisfiable, and the guarantees are not checked if
`A ∧ I ∧ R` is: the realizability check fails instead. Nor is a guarantee
checked if it failed the vacuity check, since a guarantee that never
applies always follows from the others. `check::redundancy_asked` gives
when a constraint is checked, from the outcome of asking whether `False`
can be proved from the constraints it would be compared with and itself
(`consistent_q`). That question is not asked once a vacuity query of the
procedure has answered `Sat`. That query's hypotheses are `A`, `I`, `R` and
a trigger, so `A ∧ I ∧ R`, and `A` with it, are satisfiable, and
`consistent_q` is `Sat` for both.

```fren
set_option fren.evidence "enumerated" in
pub proc redundancy_asked(
    consistent_q: Outcome,
    vacuous?,              -- it failed the vacuity check
): (det asked?) {
    ensure asked: asked? iff (consistent_q != Unsat and not vacuous?)
}
```

`check::non_redundancy` gives the verdict, from the outcome `q` of the
query:

```fren
set_option fren.evidence "enumerated" in
pub proc non_redundancy(
    q: Outcome,            -- can the constraint be proved from the others?
): (det verdict: Verdict) {
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
index in a constraint, a definition or an argument of a call, with its guard `G`, Fren
asks whether `0 <= i < q.len` can be proved from `G` and the
hypotheses of where it is written:

| Where | Hypotheses |
|---|---|
| an assumption | the other assumptions |
| a guarantee, expectation, cover goal or definition | `A`, `I` and `R`, as for vacuity |
| an argument of a call | `A`, and the calls declared before it |
| a global expectation's expectation, cover goal or definition | `A` and `I`, as for vacuity |
| a precondition of a function | the function's other preconditions |
| a function's body or postcondition | the function's preconditions |
| the value of a constant | none |

A guarantee's own `R` is among its hypotheses, so a guarantee can
ensure its own definedness through another, such as `ensure long: q.len >
3` beside `ensure third: q[3] = x`: the system meets both or neither. A
procedure with no index has no definedness results. `check::definedness`
decides each query like an expectation, and a model is a counterexample,
reported at the `[` of the index:

```fren
pub proc definedness(
    q: Outcome,            -- can `0 <= i < q.len` be proved from the guard and the hypotheses?
): (det verdict: Verdict, det reports_cex?) {
    call as_expect := expectation(q)

    ensure like_expect: verdict = as_expect.verdict and (reports_cex? iff as_expect.reports_cex?)
}
```

## Pattern types

The pattern-type check is part of [definedness](#definedness), whose
results it gives. A value given where a [subset type](Lang/SubsetTypes.md) is
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
their own pattern types. A call's argument is checked instead by the
[call check](#call-assumptions). A procedure or item with no
such value has no pattern-type results. `check::pattern_obligation`
decides each query like an expectation, and a model is a counterexample,
reported at the value:

```fren
pub proc pattern_obligation(
    q: Outcome,            -- can `e is P` be proved from the guard and the hypotheses?
): (det verdict: Verdict, det reports_cex?) {
    call as_expect := expectation(q)

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
set_option fren.evidence "enumerated" in
pub proc completeness_asked(
    unguarded_exhaustive?,    -- its arms without guards are exhaustive
): (det asked?) {
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
pub proc flat_completeness_asked(
    arms: Seq<FlatArm>,      -- the arms, in order
): (asked?) {
    use self::FlatArm::{A, B, C, Wild}

    ensure rule: asked? iff not (Wild in arms or (A in arms and B in arms and C in arms))

    -- An arm with a guard names nothing: a `match` that needs it is asked about.
    expect guarded_needed: when arms = [FlatArm::GuardedA, B, C], asked?
}

set_option fren.lint.undecidable "allow" in
expect flat_completeness_refines(arms: Seq<check::FlatArm>) {
    use check
    call concrete := flat_completeness_asked(arms)
    refines concrete completeness_asked(check::FlatArm::Wild in (arms) or (check::FlatArm::A in (arms) and check::FlatArm::B in (arms) and check::FlatArm::C in (arms)))
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
that meets its preconditions, not only those that a procedure passes it. `check::completeness` decides each query like an expectation, and a
model is a counterexample, a value of the variables for which no arm is
taken, reported at the `match`'s `match` (`F0625`), at the table's
`table` (`F0618`), or at the `table` of a [table over a
scrutinee](Lang/Expressions.md#tables-over-a-scrutinee), which is asked
about as the `match` it means is (`F0637`):

```fren
pub proc completeness(
    q: Outcome,            -- can `(P_1 and C_1) or ... or (P_n and C_n)` be proved from the guard and the hypotheses?
): (det verdict: Verdict, det reports_cex?) {
    call as_expect := expectation(q)

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
[reachability](#reachability), without the constraint, definition or
argument that the table is in. `D_i` says that the indexes in `C_i` are in
range where `C_i` evaluates them, under the guards within `C_i` alone (see
[Sequences](Lang/Expressions.md#sequences)), and is `true` if it has none.
A row's condition is evaluated only where the earlier rows' fail, so an
index in it may rest on them: in `table { q = [] => 0, q[0] > 0 => 1, _
=> 2 }`, `q[0]` is defined wherever it is evaluated, and the two rows do
not overlap, though `q[0] > 0` could hold of the unknown value of `[][0]`.

The arms of a [table over a
scrutinee](Lang/Expressions.md#tables-over-a-scrutinee) are asked about
the same way, each two arms `i < j` that
[`lang::table_arm_pair`](Lang/Expressions.md#tables-over-a-scrutinee)
asks about: those whose patterns overlap, of which one has a guard. With
`T_i` for `P_i and C_i`, that arm `i` is taken where it is tried, as for
[completeness](#completeness), and `D_i` for the indexes in its guard,
Fren asks whether `not (D_i and D_j and T_i and T_j)` can be proved.

The enclosing constraint is left out for the reason that reachability
leaves it out: it holds of a behaviour only where the table has the value
it needs, so it would hide two rows that overlap where it does not, as
in `ensure r: table { x > 0 => true, x >= 0 => false, _ => false }`,
which holds only where `x <= 0`. Each pair is its own check, so the
message can name both rows. `check::disjointness` decides each query like
an expectation, and a model is a witness, a value of the variables for
which both rows hold, reported at the condition of the later row
(`F0619`), or for which both arms are taken, at the pattern of the later
arm (`F0636`):

```fren
pub proc disjointness(
    q: Outcome,            -- can `not (D_i and D_j and C_i and C_j)` be proved from the guard and the hypotheses?
): (det verdict: Verdict, det reports_witness?) {
    call as_expect := expectation(q)

    ensure like_expect: verdict = as_expect.verdict and (reports_witness? iff as_expect.reports_cex?)
}
```

`check::disjoint_question` states what the goal of the question about
two cases is, in each behaviour: from what each case does there, as
[`lang::guarded_match`](Lang/Expressions.md#matches) has it, with its
`ArmAt` again here (a row's pattern is `_`, which matches, and its guard its condition), and
whether the indexes in each case's guard or condition are in range there.
The goal fails exactly where both cases are `Taken` and their indexes are
in range:

```fren
pub enum ArmAt { NoMatch, GuardFails, Taken }
pub enum Indexes { Defined, Undefined }

set_option fren.lint.undecidable "allow" in
pub proc disjoint_question(
    arms: Seq<ArmAt>,            -- what each case does here, in order
    defined: Seq<Indexes>,       -- whether the indexes in each case's guard are in range here
    i: Int,                      -- the earlier case
    j: Int,                      -- the later case
): (
    goal?,                       -- the goal of the question about `i` and `j` here
) {
    use self::ArmAt::Taken
    use self::Indexes::Defined

    assume pair: 0 <= i < j < arms.len and defined.len = arms.len

    ensure rule: goal? iff not (defined[i] = Defined and defined[j] = Defined and arms[i] = Taken and arms[j] = Taken)

    -- Where one of them is not taken, they do not overlap here.
    expect apart: when arms[i] != Taken, goal?
}
```

A `_` row holds wherever no earlier row does, so it overlaps none, and is
in no disjointness check, and so is a last arm `_` without a guard. The
checks of a table are on its conditions and patterns alone: a row's value
can be the same as another's, and the rows still overlap. The arms of a
`match` are not checked for disjointness: they are told apart by their
order, and an arm with a guard is usually followed by one that its
guard's failure leads to, as in `Eq if bound = 0 => AtStart, Eq =>
Other`.

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
set_option fren.evidence "enumerated" in
pub proc reachability_asked(
    guarded?,                -- the arm has a guard
    after_guard?,            -- some arm before it has a guard
): (det asked?) {
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
pub proc arms_asked(
    guards: Seq<GuardOf>,    -- whether each arm has a guard, in order
    j: Int,                  -- the arm asked about, by its position
): (asked?) {
    use self::GuardOf::Guarded

    ensure rule: asked? iff 0 <= guards.index_of([Guarded], 0) <= j
}

set_option fren.lint.undecidable "allow" in
expect arms_asked_refines(guards: Seq<check::GuardOf>, j: Int) {
    use check
    call concrete := arms_asked(guards, j)
    refines concrete reachability_asked(0 <= (j) < (guards).len and (guards)[(j)] = check::GuardOf::Guarded, 0 <= (guards).index_of([check::GuardOf::Guarded], 0) < (j))
}
```

For arm `j`, with `P_k` and `C_k` as for [completeness](#completeness),
`T_k` for `P_k and C_k`, that arm `k` is taken if no arm before it is,
`F_j` for `not T_1 and ... and not T_(j-1)`, and the `match`'s guard `G`,
Fren asks whether `not (F_j and T_j)` can be proved from `G` and the
hypotheses of where the `match` is written, as for
[completeness](#completeness), but without the constraint, definition
or argument that the `match` is in. That constraint holds of a behaviour
only where its `match` has the value it needs, so it would rule out the
arms whose values it does not need: in `ensure r: match k { Kind::A if
ok? => true, _ => false }`, `r` holds only where the first arm is taken,
yet the last arm is how `r` says what it rules out, and is not dead. If
it can be proved, no behaviour that the other hypotheses allow
takes the arm, and the check fails, at the arm's pattern (`F0626`), for
a table, at the row's condition or its `_` (`F0627`), or, for a [table
over a scrutinee](Lang/Expressions.md#tables-over-a-scrutinee), which is
asked about as the `match` it means is, at the arm's pattern (`F0638`). So a guard that is
`false`, or that contradicts the arm's pattern or the hypotheses, fails it,
and so does an arm after others that take every case it would, as `x >= 0`
after `x > 0` and `x = 0` does, or a table's `_` row after rows of which
one always holds. `check::reachability` decides each query like
[vacuity](#vacuity), whose query also asks whether something can hold:

```fren
set_option fren.evidence "enumerated" in
pub proc reachability(
    q: Outcome,            -- can `not (F_j and T_j)` be proved from the guard and the hypotheses?
): (det verdict: Verdict) {
    call as_vacuity := non_vacuity(q)

    ensure like_vacuity: verdict = as_vacuity.verdict
}
```

A model is a behaviour that takes the arm, which is not reported: a pass
is silent.

`check::split_questions` states what the goals of these questions are,
in each behaviour, from what each arm of the `match` does there, as
[`lang::guarded_match`](Lang/Expressions.md#matches) has it, with its
`ArmAt` again here, as for [disjointness](#disjointness). The goal of
arm `j`'s reachability is that `j` is not the arm taken, so the check
fails exactly when no behaviour that the hypotheses allow takes it; the
goal of completeness is that some arm is taken. Of a table, each row is
`Taken` where its condition holds, else `GuardFails`, and a `_` row is
`Taken`. The arm taken is found as there, and `k` stands for any
position, as there:

```fren
set_option fren.lint.undecidable "allow" in
pub proc split_questions(
    arms: Seq<ArmAt>,        -- what each arm does here, in order
    j: Int,                  -- the arm whose reachability is asked about
    k: Int,                  -- any position, for `none_before`
): (
    first: Int,
    reach_goal?,             -- the goal of arm `j`'s reachability question here
    complete_goal?,          -- the goal of the completeness question here
) {
    use self::ArmAt::Taken

    assume an_arm: 0 <= j < arms.len
    out first := arms.index_of([Taken], 0)  -- the position of the arm taken, `-1` if none is

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
and disjointness leave out the constraint, definition or argument that the
`match` or table is in, as above: a definition's equation in `D` too, so that in
`let y: Int := match x { n if n > 0 => 1, _ => 2 }` beside `ensure q: y =
1`, the last arm is reachable, as it would be in an `ensure`. For an
assumption, and an argument, whose call is not among its hypotheses,
that is already so.
`check::reach_hypothesis` states which of the hypotheses of definedness
reachability and disjointness ask under:

```fren
set_option fren.evidence "enumerated" in
pub proc reach_hypothesis(
    definedness?,            -- the hypothesis is one of the definedness check's at the `match`
    enclosing?,              -- it is the constraint, definition or argument that the `match` is in
): (det used?) {
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

pub proc reach_hypotheses(
    hyps: Seq<HypAt>,        -- the hypotheses, in order
    k: Int,                  -- a hypothesis, by its position
): (
    used?,                   -- reachability asks under hypothesis `k`
) {
    use self::HypAt::Definedness

    ensure rule: used? iff (0 <= k < hyps.len and hyps[k] = Definedness)

    -- The item that the case is in is never among them.
    expect not_enclosing: when 0 <= k < hyps.len and hyps[k] = HypAt::Enclosing, not used?
}

expect reach_hypotheses_refines(hyps: Seq<check::HypAt>, k: Int) {
    use check
    call concrete := reach_hypotheses(hyps, k)
    refines concrete reach_hypothesis(0 <= (k) < (hyps).len and (hyps)[(k)] != check::HypAt::Other, 0 <= (k) < (hyps).len and (hyps)[(k)] = check::HypAt::Enclosing)
}
```

## Preconditions

For each application `f(a_1, ..., a_n)` of a function `f` with
[preconditions](Lang/Items.md#contracts), with its guard `G`, and each
precondition `P` of `f`, Fren asks whether `P`, with the arguments for the
parameters, can be proved from `G` and the hypotheses of where the
application is written, as for [definedness](#definedness): this is the
[call check](#call-assumptions) for a function. The guard is read
as an index's is (see [Sequences](Lang/Expressions.md#sequences)), so in
`kind(t) = SetTy and elem(t) = u`, `elem(t)` is evaluated only where
`kind(t) = SetTy`. An application in a precondition of another function
`g` is checked under `g`'s other preconditions, and one in `g`'s body or
postconditions under all of them, for every value of `g`'s parameters
that meets them. An application, or an index or a table, in a
[closure's](Lang/HigherOrder.md#arguments) body is checked where the
closure is unfolded: at each application of the function parameter that it
is given for, under the guards around it in the higher-order function's
body and at its arguments (`lang::closure_obligation`), and is reported at
the closure. Each application and precondition is its own check, so
the message can name the precondition. `check::precondition` decides each
query like an expectation, and a model is a counterexample, reported at
the name of the applied function:

```fren
pub proc precondition(
    q: Outcome,            -- can `P(a_1, ..., a_n)` be proved from the guard and the hypotheses?
): (det verdict: Verdict, det reports_cex?) {
    call as_expect := expectation(q)

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
pub proc precondition_at(
    pres: Set<Argument>,        -- the arguments that meet the precondition
    guarded: Set<Argument>,     -- the arguments where the application's guard holds
): (det verdict: Verdict, det reports_cex?) {
    ensure rule: verdict = (if guarded subset pres then Pass else Fail)
    ensure cex: reports_cex? iff verdict = Fail

    expect unguarded: when guarded = {}, verdict = Pass
}

expect precondition_detail(pres: Set<check::Argument>, guarded: Set<check::Argument>) {
    use check
    call concrete := precondition_at(pres, guarded)
    refines concrete precondition(if (guarded) subset (pres) then check::Outcome::Unsat else check::Outcome::Sat)
}
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
so the procedure opts out:

```fren
set_option fren.lint.undecidable "allow" in
pub proc application_contract(
    pres: Seq<Bool>,       -- the function's preconditions, in order, at the arguments
    posts: Seq<Bool>,      -- its postconditions, in order, at the arguments and the application's value
    guarded?,              -- the application's guard holds
    k: Int,                -- any clause
): (
    det asks?,             -- the application asks a question of precondition `k`
    det question?,         -- the question's goal holds
    det brings?,           -- the application brings a fact of postcondition `k`
    det fact?,             -- the fact holds
) {
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
definition, as an expectation is a claim about a procedure. The query
has no quantifier, since the parameters are its variables. A model is a
counterexample, the values of the parameters, reported at the
postcondition's name. An uninterpreted function's postconditions are not
checked: they are what is known of it, which each application brings to
its queries as `N` (see [above](#checks)), and an
[interpretation](Impl.md#interpretations) in Lean proves them.
`check::postcondition` decides each query like an expectation:

```fren
pub proc postcondition(
    q: Outcome,            -- can `Q` be proved from the function's preconditions?
): (det verdict: Verdict, det reports_cex?) {
    call as_expect := expectation(q)

    ensure like_expect: verdict = as_expect.verdict and (reports_cex? iff as_expect.reports_cex?)
}
```

`check::postcondition_at` states it in detail, over the same domain: a
defined function whose preconditions hold at the arguments `pres`, and
whose postcondition holds, of the body's value, at the arguments `posts`.
Its implementation builds the body's procedure with the function's
preconditions and postcondition, and runs the real check, with a solver
that tries every argument. It refines `check::postcondition`:

```fren
pub proc postcondition_at(
    pres: Set<Argument>,      -- the arguments that meet the preconditions
    posts: Set<Argument>,     -- the arguments where the postcondition holds
): (det verdict: Verdict, det reports_cex?) {
    ensure rule: verdict = (if pres subset posts then Pass else Fail)
    ensure cex: reports_cex? iff verdict = Fail

    expect everywhere: when posts = {Argument::A0, Argument::A1}, verdict = Pass
}

expect postcondition_detail(pres: Set<check::Argument>, posts: Set<check::Argument>) {
    use check
    call concrete := postcondition_at(pres, posts)
    refines concrete postcondition(if (pres) subset (posts) then check::Outcome::Unsat else check::Outcome::Sat)
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

pub fn refutes?(Set<ConstraintName>)   -- the constraints entail the failure

set_option fren.lint.undecidable "allow" in
pub proc minimal(
    candidates: Set<ConstraintName>,
    core: Set<ConstraintName>,
    dropped: ConstraintName,            -- any one constraint, for the minimality condition
): (det minimal?) {
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

An output declared with `det`, a result or an `exists` or `let` variable
(see [Procedures](Lang/Procedures.md#members)), must be determined by the
procedure's inputs: any two behaviours that satisfy `I` and `R` on the
same admissible input agree on it. For each `det` output `x`, Fren takes a
second copy `y'`, `o'` of the call variables and outputs, and asks whether
`x = x'` can be proved from

  A(i) ∧ I(i, y) ∧ R(i, y, o) ∧ I(i, y') ∧ R(i, y', o')

The call variables are copied too, so an output that depends on a
call's output which is not itself determined is not determined either.
The functions are not copied: both copies are under the same
[interpretation](#interpretations), so an output that is a function of the
inputs, as in `ensure r: x = f(i)`, is determined. `check::copied` gives what
the second copy renames:

```fren
pub enum Symbol { Input, InstanceVariable, Output, Function }

set_option fren.evidence "enumerated" in
pub proc copied(symbol: Symbol): (det copied?) {
    ensure rule: copied? iff symbol is Symbol::InstanceVariable | Symbol::Output

    expect shared_interpretation: when symbol = Symbol::Function, not copied?
}
```

A model is a counterexample: Fren reports the inputs, and the two values of
`x`.

`check::determinism` decides each query like an expectation:

```fren
pub proc determinism(
    q: Outcome,            -- can `x = x'` be proved from both copies?
): (det verdict: Verdict, det reports_cex?) {
    call as_expect := expectation(q)

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

`set_option fren.evidence "tested" in` before a procedure, an expectation
or global expectation, a call or a `det` output sets the evidence of its
checks to *testing*; `"solver"`, the default, sets it back. Before a
procedure, it sets that of all the procedure's checks, and before a member
or result, that of its checks, which takes precedence:

| Before | Its checks |
|---|---|
| an expectation | the expectation, its vacuity, and the definedness, completeness, disjointness, reachability and preconditions of what it reads |
| a cover goal | the cover goal, and the definedness, completeness, disjointness, reachability and preconditions of what it reads |
| a call | the call's assumptions, and the definedness, completeness, disjointness, reachability and preconditions of its arguments |
| a `det` output | its determinism |
| a procedure | all of the procedure's checks |
| a global expectation | all of its checks, as before a procedure |
| a [refinement](Lang/Refinement.md) | all of the checks of its obligation, including the definedness of the arguments of the abstract procedure's calls |

As with a [lint setting](Lint.md), `set_option` without `in` sets the
evidence of every later procedure, global expectation and
[refinement](Lang/Refinement.md) in the file, and
before any other item it sets nothing. Within a procedure, the setting must
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
reaches no conclusion leaves it inconclusive, with the same warnings. A
check whose tests would evaluate an [unbounded
quantifier](Lang/Quantifiers.md#unbounded-quantifiers) that the evaluator
cannot enumerate, one with a bound name without a
[domain](Lang/Quantifiers.md#guards), is not run, and the quantifier is an
error (`F0639`), as [Evaluation](Eval.md#quantifiers) says: such a check
needs the solver's evidence, or a `trusted` claim. The
checks that testing cannot decide are not run: vacuity and redundancy,
which ask whether something can hold at all, which a failed search does
not refute; definedness, since an index out of range has no value
that the evaluator knows (see [Evaluation](Eval.md#searching-for-behaviours)),
so testing can neither pass nor fail it, though the definedness of a value
given where a pattern type is declared is still the solver's
(`check::by_evidence`); completeness, disjointness and
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
procedure, in which the goal holds, is a witness, and passes it. Testing
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

pub proc by_testing(
    kind: Kind,
    tested?,               -- the check's evidence is testing
): (det run: Run) {
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

    ensure rule: run = table {
        | not tested? => BySolver,
        | tested? and not kind in {Vacuity, Redundancy, Definedness, Completeness, Disjointness, Precondition, Reachability} => ByTesting,
        | tested? and kind in {Vacuity, Redundancy, Definedness, Completeness, Disjointness, Precondition, Reachability} => Skipped,
    }

    expect never_both: when tested?, run != BySolver
}
```

## Checking by enumeration

A check can also be decided by *enumerating* behaviours, smallest first,
instead of asking the solver, in the style of SmallCheck (Runciman, Naylor
and Lindblad, "SmallCheck and Lazy SmallCheck", Haskell '08) and of fair
enumeration (New, Fetscher, Findler and McCarthy, "Fair enumeration
combinators", JFP 2017). Where every variable has finitely many values,
enumeration sees every behaviour, so its verdict is a decision, as strong
as the solver's, with no solver and no time limit; elsewhere it sees every
behaviour up to a size, which is evidence of its own, weaker than a proof
and unlike testing's.

The evidence setting of [Checking by testing](#checking-by-testing) takes
two more values:

```
evidence-setting := "set_option" "fren.evidence" STRING
size-setting     := "set_option" "fren.enumeration.size" NUMBER ["in" item]
```

- `"enumerated"` decides the checks by enumeration, up to the size bound;
- `"enumerated+tested"` decides them by enumeration too, and where
  enumeration is not complete, also tests them, as `"tested"` does, with
  random behaviours beyond the bound (see [Enumeration then
  testing](#enumeration-then-testing)).

Any other value but `"solver"` and `"tested"` is the error `F0214`. A value
sets the same checks as `"tested"` does, before a procedure or a member.
`set_option fren.enumeration.size N`, before an item with `in`, or alone,
for the rest of the file, as `fren.evidence` is, sets the size bound of
the checks that the later items set to enumeration; the default is 3. A
bound above 64 is the error `F0154`, at the number, and the default is
used instead. Before a member, it is `F0216`, as any option but
`fren.evidence` is.

`check::evidence_value` gives what each value sets, and `check::by_evidence`
how each check is run:

```fren
pub enum EvidenceValue { Solver, Tested, Enumerated, EnumeratedTested, Other }

pub enum Method { Solver, Testing, Enumeration, EnumerationThenTesting, Skipped }

set_option fren.evidence "enumerated" in
pub proc evidence_value(value: EvidenceValue): (det valid?, det tested?, det enumerated?) {
    use self::EvidenceValue::{Enumerated, EnumeratedTested, Other, Tested}

    ensure valid: valid? iff value != Other
    ensure testing: tested? iff value in {Tested, EnumeratedTested}
    ensure enumeration: enumerated? iff value in {Enumerated, EnumeratedTested}

    expect invalid_sets_nothing: when not valid?, not tested? and not enumerated?
}

-- The checks that testing decides (`check::by_testing`).
pub fn testable?(kind: Kind) :=
    not kind in {Kind::Vacuity, Kind::Redundancy, Kind::Definedness, Kind::Completeness, Kind::Disjointness, Kind::Precondition, Kind::Reachability}

-- The checks that enumeration decides: all but definedness, whose indexes
-- only sequences have, and postconditions, which only bodies have.
pub fn enumerable?(kind: Kind) := not kind in {Kind::Definedness, Kind::Postcondition}

pub proc by_evidence(
    kind: Kind,
    tested?,               -- the check's evidence includes testing
    enumerated?,           -- the check's evidence includes enumeration
    obligation?,           -- a definedness check of a value given where a pattern type is declared
): (det method: Method) {
    use self::Kind::{Definedness, Redundancy, Vacuity}
    use self::Method::{Enumeration, EnumerationThenTesting, Skipped, Solver, Testing}
    assume obligation_definedness: when obligation?, kind = Definedness

    ensure rule: method = table {
        | obligation? => Solver,
        | not obligation? and not tested? and not enumerated? => Solver,
        | not obligation? and tested? and not enumerated? and testable?(kind) => Testing,
        | not obligation? and enumerated? and enumerable?(kind) and not tested? => Enumeration,
        | not obligation? and enumerated? and enumerable?(kind) and tested? => EnumerationThenTesting,
        | not obligation? and tested? and not enumerated? and not testable?(kind) => Skipped,
        | not obligation? and enumerated? and not enumerable?(kind) => Skipped,
    }

    expect obligations_solved: when obligation?, method = Solver
    expect never_solver: when (tested? or enumerated?) and not obligation?, method != Solver
    expect satisfiability_enumerated: when enumerated? and not tested? and kind in {Vacuity, Redundancy}, method = Enumeration
}
```

Vacuity and redundancy, which testing cannot decide, enumeration can: it
sees every behaviour up to the bound, so a witness that it finds is one,
and finding none is a decision where it sees every behaviour. So can it
decide completeness, disjointness, reachability and preconditions, which
are about where an expression is evaluated: where no row of a table holds,
the table's value is the interpretation's unspecified value of its type,
which enumeration enumerates too (see [Searching](#searching)), as the
solver leaves it unconstrained. The definedness of indexes is not run:
they are of sequences, which are not enumerable. A value given where a
pattern type is declared is the solver's to check, whatever the evidence,
for testing too: neither testing nor enumeration decides it, and dropping
it would leave a value outside its type unreported (`F0661`).

The default stays `"solver"`, and `"tested"` stays testing alone: most
checks set to testing are about strings, sets and sequences, which are
not yet enumerable (below), so enumerating them first would make them
errors; and a spec that sets `"tested"` has chosen evidence that Lean does
not run, which a combined default would change.

### Enumerable types

Enumeration needs every variable's type to be *enumerable*: `Bool`, `Int`
and `Nat`, an enumeration, recursive or not, a record, a newtype, an
instance of a generic type, a pattern type, and an abstract type, with the
types within it enumerable too. `String`, sets, relations and sequences
are not yet. A variable whose type brings no constraint, such as a
call's input, which the call check asks of its argument, ranges
over its type without patterns. A procedure, or a global expectation,
with a variable of another type, that applies an uninterpreted function
with a [contract](Lang/Items.md#contracts), whose postconditions constrain
its interpretations, or a [generic
one](Lang/GenericFunctions.md#uninterpreted-generic-functions), each of
whose instances is a function of its own, or that has an unbounded
quantifier is not enumerated: it is the error `F0645`, at it, and none of its checks set to
enumeration is run.

### Sizes and order

The values are the [values](Lang/Semantics.md#values) of `lang::Value`, and
an abstract type's values those of an interpretation. Each type is
unfolded, for the size bound `n`, into a *shape*, a finite tree: a recursive enumeration's payloads are unfolded `n` deep, since a
variant's payload is one smaller than it. Each value has a *size*:

| Value | Size |
|---|---|
| `true`, `false` | 0 |
| an `Int` `i` | `|i|` |
| a `Nat` `k` | `k` |
| an integer of a finite integer pattern type | 0 |
| the `k`th value of an abstract type | `k` |
| a variant without a payload | 0 |
| a variant with a payload | one more than the largest size of its payload's values |
| a record or a newtype | the largest size of its fields, 0 if it has none |
| a value of any other pattern type | its size in its base type |

`check::value_size` states it, over the kind of value, the integer it is,
for an integer or an abstract type's value, and the largest size of its
parts:

```fren
pub enum Sized { Boolean, Integer, Natural, FiniteInteger, AbstractValue, Nullary, WithPayload, Record }

pub proc value_size(
    kind: Sized,
    value: Int,          -- an integer's value, or the position of an abstract type's value
    largest: Nat,        -- the largest size of its payload's or fields' values, 0 if it has none
): (det size: Nat) {
    use self::Sized::{AbstractValue, Integer, Natural, Record, WithPayload}
    assume natural: when kind in {Natural, AbstractValue}, value >= 0

    ensure rule: size = match kind {
        Integer => value.abs,
        Natural | AbstractValue => value,
        WithPayload => largest + 1,
        Record => largest,
        _ => 0,
    }

    expect payload_larger: when kind = WithPayload, size > largest
}
```

The enumeration of a shape lists each of its values of size at most `n`
exactly once, with its size, and nothing else: `check::listed`, where
`value?` says that a value, with a size, is the shape's, by the shape's
typing rules, which mirror the table, and `times` is how many times the
enumeration lists the pair. It is proved of the enumerator
(`Shape.vals` in `FrenCore.Enumeration`) for every shape:

```fren
pub proc listed(
    value?,              -- the value, with the size, is one of the shape's
    size: Nat,
    bound: Nat,
): (
    det times: Nat,          -- how many times the enumeration lists it
) {
    ensure exactly_once: times = if value? and size <= bound then 1 else 0

    expect complete: when value? and size <= bound, times = 1
    expect nothing_else: when not value?, times = 0
}
```

Of these, the values of a type of finitely many values are all of size at
most some bound; so for a large enough bound the enumeration is *complete*,
every value of the type, as in FEAT (Duregård, Jansson and Wang, Haskell
'12), whose finite types the enumeration exhausts. A shape is *exhausted*
at the bound when every value of the type it stands for has size at most
it: it is `Bool`, a finite integer pattern type, or built of exhausted
shapes, and no variant's payload was cut off by the unfolding.

The values are listed smallest first, and in the structural order among
those of a size: variants in order, and payloads and fields by their
values' order, the first varying slowest; integers `0, 1, -1, 2, -2, ...`;
a finite integer pattern type's in increasing order. `check::smallest_first`:

```fren
pub proc smallest_first(
    earlier?,            -- the first value is listed before the second
    first: Nat,          -- the first value's size
    second: Nat,         -- the second value's size
): (det ordered?) {
    ensure rule: ordered? iff (not earlier? or first <= second)

    expect sorted: when earlier?, ordered? iff first <= second
}
```

and the enumerator meets it with `ordered?` always true.

### Searching

A procedure's *slots* are its variables whose values are enumerated: its
own and its calls', but not those with definitions, which are computed
from their definitions, then a second copy of each that determinism
copies, and last, a *hidden* slot for each type whose unspecified value
some constraint reads, where no row of a table holds: the interpretation's
value, which an abstract type's values are, as with the solver (see
[Interpretations](#interpretations)), and then a hidden slot for each
uninterpreted function that a constraint applies, whose values are its
interpretations: tables from the tuples of its arguments up to the bound
to its results up to the bound, each as large as its largest result, so
that over finite types every interpretation is among them. An argument
beyond the bound gets the first result, which extends the table to an
interpretation. Each slot holds the values of its type up to the bound,
smallest first.

Each query of the [checks](#checks) is answered by searching the
assignments of the slots that its formulas read, the variables that they
mention (their [free variables](Lang/EvaluationRules.md#free-variables)), for
one that makes its hypotheses true and its goal false: `sat`, with that assignment as its
model, or `unsat` if there is none. The assignments are searched fairly,
by *level*, the largest size of an assignment's values: every assignment
of level 0, then of level 1, up to the bound, and within a level in the
order of the slots and of each slot's values, the last slot varying
fastest. So no slot starves the others, and the model is the smallest:
of the least level, and the first of that level. A model gives the slots
that the query reads, as a solver's gives the variables that it mentions,
and the defined variables that it mentions, by their definitions. Each
hypothesis is evaluated as soon as the slots it reads are set, which
changes how fast the search is, not which model it finds. `∃ outputs`
searches every value of the outputs up to the bound.

The search is the same in both front ends, over the same slots and values
in the same order, so they find the same models, and report the same
counterexamples and minimal sets, which the shared check algorithms
compute from the answers as they do from the solver's.

The search's soundness rests on four facts, each proved of the real
functions of `FrenCore.Enumeration` (in `Impls/Enumeration.lean`):

- *The slots suffice* (`check::slots_suffice`): a formula's value depends
  only on the slots that `EF.slots` gives it, given that each constraint's
  depends only on the slots it reads, and each defined variable's on those
  of its definition, through the definitions it mentions. So every slot
  that a check's outcome depends on is searched, a defined variable's
  definition's too.
- *Pruning is conservative* (`check::pruning`): trying each part as soon as
  the slots it reads are chosen, and not extending a choice that fails
  one, finds the first choice of the order that makes every part true.
- *The order is fair* (`check::fair_order`): it lists every assignment up
  to the bound, each once, by level, smallest first, so no slot starves
  the others; given that the values of each slot of size at most `k`, up
  to the bound, are its first ones, as the order of
  [values](#sizes-and-order) makes them.
- *The search finds the first* (`check::search_first`): its model is the
  first assignment of the fair order that makes every part true.

A shape *exhausted* at the bound has no value beyond it
(`check::shape_bound`), so an exhausted search sees every behaviour.

```fren
pub proc slots_suffice(
    atoms_local?,            -- each constraint's value depends only on the slots it reads
    definitions_local?,      -- each defined variable's on those of its definition
    outputs_distinct?,       -- no output has two slots
    agree?,                  -- two assignments agree on the formula's slots
): (
    same_value?,             -- the formula has the same value in both
) {
    ensure suffice: when atoms_local? and definitions_local? and outputs_distinct? and agree?, same_value?
}

pub proc pruning(
    local?,                  -- each part's value depends only on the slots it reads
    distinct?,               -- the slots chosen are distinct
): (
    first?,                  -- the choice found is the first of the order that makes every part true
) {
    ensure conservative: when local? and distinct?, first?
}

pub proc fair_order(
    ordered?,                -- each slot's values up to a size are its first ones
    within?,                 -- an assignment chooses, for each slot, one of its values up to the bound
    earlier?,                -- one assignment of the order comes before another
): (
    listed?,                 -- the order lists the first assignment
    times: Nat,              -- how many times it does
    first_level: Nat,            -- the level of the earlier assignment
    second_level: Nat,           -- the level of the later one
) {
    ensure complete: when ordered? and within?, listed?
    ensure once: when ordered?, times = if listed? then 1 else 0
    ensure smallest_first: when ordered? and earlier?, first_level <= second_level
}

pub proc search_first(
    local?,                  -- each part's value depends only on the slots it reads
    reads?,                  -- the parts read some slot
): (
    first?,                  -- the search's model is the first assignment of the fair order that makes every part true
) {
    ensure finds_first: when local? and reads?, first?
}

pub proc shape_bound(
    exhausted?,              -- the shape is exhausted at the bound
    bound: Nat,
): (
    value?,                  -- a value, with a size, is one of the shape's
    size: Nat,
) {
    ensure within: when exhausted? and value?, size <= bound
}
```

The number of assignments a procedure's enumeration searches is the
product of its slots' numbers of values, its second copies' too if
determinism is enumerated. Above 65,536, it is the error `F0644`, which
gives the number, and none of its checks set to enumeration is run
(`check::enumeration_limit`):

```fren
pub const MAX_BEHAVIOURS: Int := 65536

pub proc enumeration_limit(
    count: Nat,          -- the assignments that its enumeration would search
): (det runs?) {
    ensure rule: runs? iff count <= MAX_BEHAVIOURS
}
```

### Verdicts of enumeration

Where every slot is exhausted, enumeration sees every behaviour, so each
answer is the solver's and each verdict a decision. Elsewhere, a model is
still a behaviour, so a `sat` answer is genuine, but an `unsat` answer only
says that no assignment up to the bound refutes the query. So a check that
passes on `unsat` (the [proved](#verdict-families) family) then passes *up
to the bound*, a weaker pass than a proof, and a check that fails on
`unsat`, such as vacuity, is inconclusive, since a larger witness may
exist. Realizability's goal has `∃ outputs` within it: its failure, a
conflict, is genuine only where the outputs are exhausted, since their
values are pinned by the input, and its contradictory assumptions rest on
`unsat`. `check::enumerated_verdict`:

```fren
pub proc enumerated_verdict(
    kind: Kind,
    verdict: Verdict,        -- what the check algorithm reaches from the search's answers
    conflict?,               -- realizability failed on a conflict, rather than contradictory assumptions
    exact?,                  -- every slot is exhausted
    outputs_exact?,          -- every slot of an output is exhausted
): (
    det reported: Verdict,
    det bounded?,            -- it holds only up to the bound
) {
    use self::Kind::{
        Completeness,
        Determinism,
        Disjointness,
        Expectation,
        InstanceAssumption,
        Precondition,
        Realizability,
    }
    use self::Verdict::{Fail, Inconclusive, Pass}

    ensure reported_rule: reported = table {
        | exact? => verdict,
        | not exact? and verdict = Pass => Pass,
        | not exact? and verdict = Fail and kind = Realizability and conflict? and outputs_exact? => Fail,
        | not exact? and verdict = Fail and kind = Realizability and not (conflict? and outputs_exact?) => Inconclusive,
        | not exact? and verdict = Fail and kind in {Expectation, InstanceAssumption, Determinism, Completeness, Disjointness, Precondition} => Fail,
        | not exact? and verdict = Fail and not kind in {Realizability, Expectation, InstanceAssumption, Determinism, Completeness, Disjointness, Precondition} => Inconclusive,
        | not exact? and verdict = Inconclusive => Inconclusive,
    }
    -- What rests on an `unsat` answer that does not see every behaviour.
    ensure bounded_rule: bounded? iff (not exact? and reported != Fail and verdict != Inconclusive
        and (verdict = Fail or kind in {Realizability, Expectation, InstanceAssumption, Determinism, Completeness, Disjointness, Precondition}))

    expect decided: when exact?, reported = verdict
    expect failures_genuine: when reported = Fail, verdict = Fail
    expect bounded_pass_proves: when reported = Pass and bounded?, kind in {Realizability, Expectation, InstanceAssumption, Determinism, Completeness, Disjointness, Precondition}
}
```

The verdict family is that of [Verdict families](#verdict-families), for
the kinds that enumeration decides. A bounded inconclusive result says
that enumeration searched every behaviour up to the bound (`F0608`).
Where some checks pass only up to the bound, each front end says how many
at the procedure, as information (`F0646`), and the summary counts them:

```text
fren: 30 passed (3 by bounded enumeration), 0 failed, 0 inconclusive, 0 redundant
```

### Enumeration then testing

With `"enumerated+tested"`, a check is enumerated, and its queries are
also tested beyond the bound: where the search finds no model up to the
bound, each query draws 100 random assignments of the slots it reads, the
`t`th taking, for each slot, its `t`th random value of a size above the
bound, at most `10 * (n + 1)` for the bound `n`, a second copy another,
and, for a slot whose values are all within the bound, one of them at
random. The random values come from a seed of the procedure's path, so
both front ends draw the same ones, whatever `--seed` and `--tests` are.
Where every slot is exhausted there is nothing beyond the bound, and the
verdict is decided as with `"enumerated"`. A model that testing finds is
genuine, like the search's: a counterexample fails the check, and a
witness passes it; testing never decides a pass, which stays one up to
the bound, and the information `F0646` then counts the tests.
`check::enumerated_answer` gives a query's answer, bound to
`answerOf`:

```fren
pub enum Found { Model, NoModel }

pub proc enumerated_answer(
    search: Found,           -- what the search up to the bound found
    testing?,                -- the check is set to `"enumerated+tested"`
    test: Found,             -- what testing beyond the bound found, if asked
): (
    det answer: Outcome,
    det from_test?,          -- the model is testing's
) {
    use self::Found::{Model, NoModel}

    ensure answer_rule: (answer = Outcome::Sat) iff (search = Model or (testing? and test = Model))
    ensure no_unknown: answer != Outcome::Unknown
    ensure test_rule: from_test? iff (search = NoModel and testing? and test = Model)

    expect search_first: when search = Model, not from_test?
    expect untested: when not testing?, (answer = Outcome::Sat) iff search = Model
}
```

### Agreement

Lean decides the checks set to enumeration itself, by evaluation: each
constraint of the procedure is compiled by Lean's evaluator into a
function of an assignment of the slots, which reads each variable's value
from its slot, with the defined variables replaced by their definitions,
the abstract types by `Nat`, whose `k` is the `k`th value, and each
unspecified value by its hidden slot's, and decides the constraint. The
search, the order, the counts and the verdicts are `FrenCore`'s, shared
with the `fren` command. So both front ends report the same results and
messages, with the same counterexamples, for the checks set to
`"enumerated"` and to `"enumerated+tested"`, whose tests both draw alike,
and are compared like any other (see [Agreement with
Lean](Cli.md#agreement-with-lean)).

## Verdict families

Each check that reaches its verdict from one outcome refines `proved` or
`satisfiable`: the checks that prove something, and the checks that ask
whether something can hold.

```fren
expect expectation_proves(q: check::Outcome) {
    use check
    call concrete := expectation(q)
    expect proof: (concrete.verdict) = check::Verdict::Pass iff (q) = check::Outcome::Unsat
    expect counterexample: (concrete.verdict) = check::Verdict::Fail iff (q) = check::Outcome::Sat
}
expect instance_assumption_proves(q: check::Outcome) {
    use check
    call concrete := instance_assumption(q)
    expect proof: (concrete.verdict) = check::Verdict::Pass iff (q) = check::Outcome::Unsat
    expect counterexample: (concrete.verdict) = check::Verdict::Fail iff (q) = check::Outcome::Sat
}
expect definedness_proves(q: check::Outcome) {
    use check
    call concrete := definedness(q)
    expect proof: (concrete.verdict) = check::Verdict::Pass iff (q) = check::Outcome::Unsat
    expect counterexample: (concrete.verdict) = check::Verdict::Fail iff (q) = check::Outcome::Sat
}
expect completeness_proves(q: check::Outcome) {
    use check
    call concrete := completeness(q)
    expect proof: (concrete.verdict) = check::Verdict::Pass iff (q) = check::Outcome::Unsat
    expect counterexample: (concrete.verdict) = check::Verdict::Fail iff (q) = check::Outcome::Sat
}
expect disjointness_proves(q: check::Outcome) {
    use check
    call concrete := disjointness(q)
    expect proof: (concrete.verdict) = check::Verdict::Pass iff (q) = check::Outcome::Unsat
    expect counterexample: (concrete.verdict) = check::Verdict::Fail iff (q) = check::Outcome::Sat
}
expect precondition_proves(q: check::Outcome) {
    use check
    call concrete := precondition(q)
    expect proof: (concrete.verdict) = check::Verdict::Pass iff (q) = check::Outcome::Unsat
    expect counterexample: (concrete.verdict) = check::Verdict::Fail iff (q) = check::Outcome::Sat
}
expect postcondition_proves(q: check::Outcome) {
    use check
    call concrete := postcondition(q)
    expect proof: (concrete.verdict) = check::Verdict::Pass iff (q) = check::Outcome::Unsat
    expect counterexample: (concrete.verdict) = check::Verdict::Fail iff (q) = check::Outcome::Sat
}
expect determinism_proves(q: check::Outcome) {
    use check
    call concrete := determinism(q)
    expect proof: (concrete.verdict) = check::Verdict::Pass iff (q) = check::Outcome::Unsat
    expect counterexample: (concrete.verdict) = check::Verdict::Fail iff (q) = check::Outcome::Sat
}
expect vacuity_witnesses(q: check::Outcome) {
    use check
    call concrete := non_vacuity(q)
    refines concrete satisfiable(q)
}
expect cover_witnesses(q: check::Outcome) {
    use check
    call concrete := cover_goal(q)
    expect witness: (concrete.verdict) = check::Verdict::Pass iff (q) = check::Outcome::Sat
    expect refuted: (concrete.verdict) = check::Verdict::Fail iff (q) = check::Outcome::Unsat
}
expect redundancy_witnesses(q: check::Outcome) {
    use check
    call concrete := non_redundancy(q)
    refines concrete satisfiable(q)
}
expect reachability_witnesses(q: check::Outcome) {
    use check
    call concrete := reachability(q)
    refines concrete satisfiable(q)
}

#fren_check
```
