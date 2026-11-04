# Reports of modules

A spec whose sentences and block members are all of today's forms keeps
its verdicts and messages under the design of #669, but for what the
instances of today's laws and induction by unfolding decide of a check
that today is Inconclusive (`module.expansion`). This chapter checks that
guarantee, *strict expansion*, over the model of
[Implementations](Lang/Implementations.md). Nothing in it takes a report or
a verdict that it could compute as an input. It computes a check's new own
verdict from its kind, today's verdict and, where today's verdict is
Inconclusive, the answer of the same query with the instances added
(`expansion::today_verdict`), the axioms that the check
rests on in the model (`lang::caveat_premise`, `lang::asked_of?`), and the
rules that show every check: [`check::reported_pass`](Evidence.md#reports)
for its verdict, `F0663` and `F0664`, and
[`check::law_premise`](Evidence.md#the-laws-of-a-trait) for `F0665`. It is
a chapter of its own, after Evidence, since a chapter of the language's
module cannot call Evidence's requirements.

```fren
pub mod expansion
```

## Verdicts under instances

**Dynamic semantics**

r[module.instance.models] expansion::today_verdict::{answers_but_unsat_change_nothing, passes_stay, failures_stay}
A model of a query whose hypotheses include instances of axioms is a
model of those instances, not always of the axioms, and is neither a
counterexample nor a witness. A check whose sentences are all of today's
forms asks today's query, today's laws quantified among its hypotheses
([Traits](Lang/Traits.md#expectations)) and its contracts as today, and
takes its verdict. Only where that verdict is Inconclusive does Fren ask
the same query with the instances added, and where that query does not
give `unsat`, the check keeps today's verdict and messages. Any other
check reports a model of the instances as a counterexample, or as a
witness, only where Fren confirms that the model meets the axioms
themselves, and is Inconclusive where it does not.

> **Note:** So no model of the instances alone is taken as a
> counterexample or as a witness, and no pass that today's query gives is
> lost, even where the instances make a query run out of time. The warning
> of a check that cannot decide whether its assumptions hold with the
> laws, as `traits::Pos::undecided` in the ui tests, stays.

r[module.expansion.instances] expansion::today_verdict::{only_undecided_changes, unsat_by_kind, induction_only_claims, lawless_unchanged, refuted_kept}, expansion::realizability_unchanged
A check of today's forms that was not decided may be decided by the
instances of today's laws, where the query with them gives `unsat`. Its
new verdict is the one that `unsat` gives a check of its kind, as
[`check::from_unsat?`](Evidence.md#the-laws-of-a-trait) states: a pass of
a proof, such as an expectation, and a failure of a witness check, a
cover goal, a vacuity, redundancy or reachability check. A check whose kind's queries have no laws,
realizability, keeps its verdict, as does one that
is Inconclusive as the solver's model contradicts Fren's semantics
([Reporting](Models.md#reporting)). An expectation's claim that is still
not decided may also pass by the induction that `module.induction.unfolding`
and `module.induction.lemmas` add to [Recursion's](Lang/Recursion.md#induction),
as `lang::induction_verdict` decides.

> **Note:** So assumptions that contradict the laws are an error
> (`F0602`) where today they are a warning that the check is not decided
> (`F0608`), and a cover goal that the laws' instances rule out fails.

```fren
use check::{
    Caveat,
    Kind,
    Verdict,
    from_unsat?,
    law_premise,
    pass_from_unsat?,
    proof?,
    query_laws?,
    reported_pass,
}

use lang::{ModuleModel, ModuleSentence, RecPost, asked_of?, caveat_premise, induction_verdict}

-- What the query with the instances added answers: `unsat`, or anything
-- else, a model or no answer.
pub enum InstancesAnswer { Unsat, Other }

-- The verdict that an `unsat` answer gives a check of the kind.
pub fn unsat_verdict(kind: Kind): Verdict :=
    if pass_from_unsat?(kind) then Verdict::Pass else Verdict::Fail

-- Whether induction may decide a check of the kind: a claim's.
pub fn induction_kind?(kind: Kind) := kind = Kind::Expectation

pub fn as_post(v: Verdict): RecPost := match v {
    Verdict::Pass => RecPost::Passed,
    Verdict::Fail => RecPost::Failed,
    Verdict::Inconclusive => RecPost::Inconclusive,
}

pub fn as_verdict(r: RecPost): Verdict := match r {
    RecPost::Passed => Verdict::Pass,
    RecPost::Failed => Verdict::Fail,
    RecPost::Inconclusive => Verdict::Inconclusive,
}

-- What the instances decide of a check: today's verdict where it was
-- decided, where the check's queries have no laws, or where its model
-- contradicts Fren's semantics, and otherwise what `unsat` gives the kind.
pub fn by_instances(kind: Kind, before: Verdict, instances: InstancesAnswer, refuted?): Verdict :=
    if before != Verdict::Inconclusive or refuted? or not query_laws?(kind) then before
    else if instances = InstancesAnswer::Unsat then unsat_verdict(kind)
    else before

set_option fren.lint.undecidable "allow" in
pub fn some_passed?(attempts: Seq<RecPost>) :=
    exists (k: Int), 0 <= k < attempts.len and attempts[k] = RecPost::Passed

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
pub proc today_verdict(
    kind: Kind,                      -- the check's kind
    before: Verdict,                 -- its verdict today: today's query, with today's laws quantified, and Recursion's induction
    instances: InstancesAnswer,      -- the answer of that query with the instances added
    refuted?,                        -- the check is Inconclusive as the solver's model contradicts Fren's semantics (Models.md#reporting)
    unfolding: Seq<RecPost>,         -- the inductions that `module.induction.unfolding` and `module.induction.lemmas` add, on each candidate
): (det after: Verdict) {
    call induced := induction_verdict(
        as_post(by_instances(kind, before, instances, refuted?)),
        refuted?,
        unfolding,
    )
    out after :=
        if induction_kind?(kind) then as_verdict(induced.reported) else by_instances(kind, before, instances, refuted?)

    expect passes_stay: when before = Verdict::Pass, after = Verdict::Pass
    expect failures_stay: when before = Verdict::Fail, after = Verdict::Fail
    expect answers_but_unsat_change_nothing: when instances = InstancesAnswer::Other and not some_passed?(unfolding),
        after = before
    expect only_undecided_changes: when after != before, before = Verdict::Inconclusive
    expect unsat_by_kind: when after != before and instances = InstancesAnswer::Unsat,
        from_unsat?(kind, after)
    expect induction_only_claims: when after != before and instances = InstancesAnswer::Other,
        proof?(kind) and induction_kind?(kind) and after = Verdict::Pass
    expect lawless_unchanged: when not query_laws?(kind), after = before
    expect refuted_kept: when refuted?, after = before
}

-- A cover goal of today's forms that is not decided today, and that the
-- laws' instances rule out, fails.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
expect cover_ruled_out() {
    call r := today_verdict(
        Kind::Cover,
        Verdict::Inconclusive,
        InstancesAnswer::Unsat,
        false,
        [],
    )
    expect fails: r.after = Verdict::Fail
}

-- A redundancy check is not decided by induction.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
expect induction_not_for_witnesses() {
    call r := today_verdict(
        Kind::Redundancy,
        Verdict::Inconclusive,
        InstancesAnswer::Other,
        false,
        [RecPost::Passed],
    )
    expect stays: r.after = Verdict::Inconclusive
}

-- Realizability's queries have no laws, so their instances change nothing.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
expect realizability_unchanged() {
    call r := today_verdict(
        Kind::Realizability,
        Verdict::Inconclusive,
        InstancesAnswer::Unsat,
        false,
        [],
    )
    expect stays: r.after = Verdict::Inconclusive
}
```

## Strict expansion

**Dynamic semantics**

r[module.expansion.computed] expansion::strict_expansion::{shown_kept, passes_stay, failures_stay, caveats_kept, only_undecided_changes, new_verdict_from_query, lawless_kept, refuted_kept}
Of a check of today's forms whose own verdict today is not Inconclusive,
everything that is shown is the same as today: its verdict, whether it is
counted among the passes by testing or by bound, `F0663`, `F0664` and
`F0665`. A pass stays a pass, and a failure a failure. A new verdict is the
one that the check's kind gives the query's answer.

r[module.expansion.induction] expansion::strict_expansion::{new_pass_reported, new_pass_caveat}
A check of today's forms that today is Inconclusive may pass, by the
instances of today's laws or by the induction that
`module.induction.unfolding` and `module.induction.lemmas` add to
[Recursion's](Lang/Recursion.md#induction), unless the solver's model of it
contradicts Fren's semantics. The new pass is reported as
every pass is, by `check::reported_pass`: it is shown as Inconclusive, with
`F0664`, where it rests on a check that is not settled, and gets `F0663`
where its caveats are more than its own method's. It carries `F0665`
exactly where `check::law_premise` gives it, from the axioms that it rests
on in the model, and from whether its item has a vacuity check under them.

r[module.expansion.corpus]
Each stage of #669 that lands compares the messages of Fren's own specs
and of the ui tests, before and after, and every difference is one that
strict expansion allows.

```fren
-- Of every check of every model, and so of every check of today's forms.
set_option fren.lint.undecidable "allow" in
expect strict_expansion(
    m: ModuleModel,
    n: ModuleSentence,               -- the check's sentence
    kind: Kind,                      -- the check's kind
    before: Verdict,                 -- its own verdict today: today's query, with today's laws quantified, and Recursion's induction
    instances: InstancesAnswer,
    refuted?,
    unfolding: Seq<RecPost>,
    own: Set<Caveat>,                -- the caveats of its own method, the same before and after
    caveats: Set<Caveat>,            -- its caveats, which the checks it rests on give, the same before and after
    settled?,                        -- it rests on no check that is not settled, before and after
) {
    assume own_within: own subset caveats
    assume witness_plain: when not proof?(kind), own = {} and caveats = {}

    call v := today_verdict(kind, before, instances, refuted?, unfolding)
    call caveat := caveat_premise(m, n)
    call old := reported_pass(kind, before, own, caveats, settled?)
    call new := reported_pass(kind, v.after, own, caveats, settled?)
    call old_laws := law_premise(kind, before, caveat.laws?, asked_of?(m, n))
    call new_laws := law_premise(kind, v.after, caveat.laws?, asked_of?(m, n))

    expect shown_kept: when before != Verdict::Inconclusive,
        new.shown = old.shown and new.by_testing? = old.by_testing? and new.by_bound? = old.by_bound?
        and new.weakened? = old.weakened? and new.unsettled? = old.unsettled?
    expect caveats_kept: when before != Verdict::Inconclusive, new_laws.rests? = old_laws.rests?
    expect passes_stay: when old.shown = Verdict::Pass, new.shown = Verdict::Pass
    expect failures_stay: when old.shown = Verdict::Fail, new.shown = Verdict::Fail
    expect only_undecided_changes: when new.shown != old.shown, old.shown = Verdict::Inconclusive
    expect new_verdict_from_query: when v.after != before,
        (instances = InstancesAnswer::Unsat and v.after = unsat_verdict(kind))
        or (induction_kind?(kind) and v.after = Verdict::Pass)
    expect lawless_kept: when not query_laws?(kind), v.after = before
    expect refuted_kept: when refuted?, v.after = before
    expect new_pass_reported: when before = Verdict::Inconclusive and v.after = Verdict::Pass,
        new.unsettled? = (not settled?) and new.weakened? = (settled? and caveats != own)
    expect new_pass_caveat: when before = Verdict::Inconclusive and v.after = Verdict::Pass,
        new_laws.rests? = (caveat.laws? and query_laws?(kind) and from_unsat?(kind, Verdict::Pass)
        and not asked_of?(m, n))
}
```

The Lean-hosted front end checks this chapter's items by name:

```fren
#fren_check today_verdict
#fren_check cover_ruled_out
#fren_check induction_not_for_witnesses
#fren_check realizability_unchanged
#fren_check strict_expansion
```
