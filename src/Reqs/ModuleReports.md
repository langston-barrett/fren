# Reports of modules

A spec whose sentences and block members are all of today's forms keeps
its verdicts and messages under the design of #669, but for what the
instances of today's laws and induction by unfolding decide of a check
that today is shown as Inconclusive, or of its premises
(`module.expansion`). This chapter checks that guarantee, *strict
expansion*, over the model of
[Implementations](Lang/Implementations.md). Nothing in it takes a report or
a verdict that it could compute as an input. It computes a check's new own
verdict from its kind, today's verdict and, where today's verdict is
Inconclusive, the answer of the same query with the instances added
(`expansion::today_verdict`). It computes the axioms that the check
rests on in the model (`lang::caveat_premise`, `lang::asked_of?`) and the
premises' own verdicts before and after (`expansion::premise_verdicts`).
It uses [`check::pass_evidence`](Evidence.md#resting-on-checks) for its
caveats and settledness, [`check::reported_pass`](Evidence.md#reports)
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
give `unsat`, the check keeps today's own verdict and the messages of
that query. Its shown verdict may still become a pass when its premises
settle (`module.expansion.computed`). Any other check reports a model of the instances as a counterexample, or as a
witness, only where Fren confirms that the model meets the axioms
themselves, and is Inconclusive where it does not.

> **Note:** So no model of the instances alone is taken as a
> counterexample or as a witness, and no pass that today's query gives is
> lost, even where the instances make a query run out of time. The warning
> of a check that cannot decide whether its assumptions hold with the
> laws, as `traits::Pos::undecided` in the ui tests, stays.

r[module.expansion.instances] expansion::today_verdict::{only_undecided_changes, unsat_by_kind, induction_only_claims, lawless_unchanged, refuted_kept}, expansion::realizability_unchanged
A check of today's forms whose own verdict was not decided may be decided
by the instances of today's laws, where the query with them gives `unsat`.
Its new own verdict is the one that `unsat` gives a check of its kind, as
[`check::from_unsat?`](Evidence.md#the-laws-of-a-trait) states: a pass of
a proof, such as an expectation, and a failure of a witness check, a
cover goal, a vacuity, redundancy or reachability check. A check whose kind's queries have no laws,
realizability, keeps its own verdict, as does one that
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
    earlier?,
    from_unsat?,
    law_premise,
    pass_evidence,
    pass_from_unsat?,
    proof?,
    query_laws?,
    reported_pass,
    rests_on,
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

r[module.expansion.computed] expansion::strict_expansion::{shown_kept, decided_only_uncapped, passes_stay, failures_stay, caveats_kept, only_undecided_changes, new_verdict_from_query, lawless_kept, refuted_kept}, expansion::laws_expansion::caveats_kept
A check of today's forms shown as a pass stays a pass, and one shown as a
failure stays a failure, with the same messages and counts by testing and
by bound. A check whose own verdict today is decided may change only from
shown Inconclusive with `F0664` to a pass, when the checks it rests on
become settled. Its own verdict and `F0665` stay the same. The caveats of
its method and premises stay the same, since `check::pass_evidence`
computes them from the methods and premise relation, independently of the
verdicts. A new own verdict is the one that the check's kind gives the
query's answer.

r[module.expansion.induction] expansion::strict_expansion::new_pass_reported, expansion::laws_expansion::new_pass_caveat, expansion::premise_becomes_settled, expansion::own_pass_becomes_settled
A check of today's forms whose own verdict today is Inconclusive may
pass, by the instances of today's laws or by the induction that
`module.induction.unfolding` and `module.induction.lemmas` add to
[Recursion's](Lang/Recursion.md#induction), unless the solver's model of it
contradicts Fren's semantics. A new own pass can also settle checks that
rest on it, so that a check already passing on its own, but shown as
Inconclusive with `F0664`, becomes a shown pass. Each new pass is reported
as every pass is, by `check::reported_pass`, using the premises' verdicts
after expansion: it is shown as Inconclusive, with `F0664`, where it still
rests on a check that is not settled, and otherwise as a pass, with
`F0663` where its caveats are more than its own method's. It carries
`F0665` exactly where `check::law_premise` gives it, from the axioms that
it rests on in the model, and from whether its item has a vacuity check
under them.

r[module.expansion.corpus]
Each stage of #669 that lands compares the messages of Fren's own specs
and of the ui tests, before and after, and every difference is one that
strict expansion allows.

```fren
-- Each check's raw query inputs, by its position. The first three
-- relations give one value per check. `unfolding` records every additional
-- induction attempt's result; their order and duplicates do not affect
-- `induction_verdict`, which asks only whether any attempt passed.
pub struct Queries {
    kinds: Rel<Int, Kind>,
    before: Rel<Int, Verdict>,
    instances: Rel<Int, InstancesAnswer>,
    refuted: Set<Int>,
    unfolding: Rel<Int, RecPost>,
}

-- One representative of each attempt result, preserving whether any
-- passed, for Recursion's sequence of induction attempts.
set_option fren.lint.undecidable "allow" in
pub fn attempts(results: Set<RecPost>): Seq<RecPost> :=
    (if RecPost::Passed in results then [RecPost::Passed] else [])
    ++ (if RecPost::Failed in results then [RecPost::Failed] else [])
    ++ (if RecPost::Inconclusive in results then [RecPost::Inconclusive] else [])

-- The finite table used to select the checks that instances can pass.
-- `premise_verdicts::kinds_agree` checks it against Evidence's decisions
-- for every kind, and `after_rule` checks the whole computation against
-- `today_verdict` at an arbitrary check.
pub const INSTANCE_PASS_KINDS: Set<Kind> := {
    Kind::Expectation,
    Kind::InstanceAssumption,
    Kind::Determinism,
    Kind::Definedness,
    Kind::Completeness,
    Kind::Disjointness,
    Kind::Precondition,
    Kind::Postcondition,
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
pub proc premise_verdicts(
    queries: Queries,
    k: Int,
    kind: Kind,                  -- the raw values at k, selected from the relations
    before: Verdict,
    instances: InstancesAnswer,
): (det after: Verdict, det unsettled_before: Set<Int>, det unsettled_after: Set<Int>) {
    require kind_at: queries.kinds.image({k}) = {kind}
    require before_at: queries.before.image({k}) = {before}
    require instances_at: queries.instances.image({k}) = {instances}

    call v := today_verdict(
        kind,
        before,
        instances,
        k in queries.refuted,
        attempts(queries.unfolding.image({k})),
    )
    out after := v.after
    let undecided: Set<Int> :=
        queries.before.inverse.image({Verdict::Inconclusive}) minus queries.refuted
    let instance_passes: Set<Int> := queries.instances.inverse.image({InstancesAnswer::Unsat})
        inter queries.kinds.inverse.image(INSTANCE_PASS_KINDS)
    let induction_passes: Set<Int> := queries.kinds.inverse.image({Kind::Expectation})
        inter queries.unfolding.inverse.image({RecPost::Passed})
    out unsettled_before :=
        queries.before.domain minus queries.before.inverse.image({Verdict::Pass})
    out unsettled_after :=
        unsettled_before minus (undecided inter (instance_passes union induction_passes))

    expect before_rule: k in unsettled_before iff before != Verdict::Pass
    expect after_rule: k in unsettled_after iff after != Verdict::Pass
    expect kinds_agree: kind in INSTANCE_PASS_KINDS iff (query_laws?(kind) and pass_from_unsat?(kind))
    expect only_settles: unsettled_after subset unsettled_before
}

-- Turn `pass_evidence`'s flags into the caveats that `reported_pass` takes.
pub fn caveats_of(random?, bounded?): Set<Caveat> :=
    (if random? then {Caveat::Random} else {}) union (if bounded? then {Caveat::Bounded} else {})

-- Of every check of every model, and so of every check of today's forms.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
expect strict_expansion(
    queries: Queries,               -- each check's own query inputs, never its report or settledness
    k: Int,                         -- the check's position
    kind: Kind,                     -- its raw kind and query answers, selected at k
    before: Verdict,
    instances: InstancesAnswer,
    methods: Rel<Int, Caveat>,       -- each method's caveats; unchanged because expansion changes no evidence setting
    premises: Rel<Int, Int>,         -- the passes each check takes as premises; unchanged for today's forms
) {
    assume kind_at: queries.kinds.image({k}) = {kind}
    assume before_at: queries.before.image({k}) = {before}
    assume instances_at: queries.instances.image({k}) = {instances}
    -- Witness checks rest on no premise and have no caveat, as Evidence
    -- states. For proof checks, use the program's methods and premises.
    let own: Rel<Int, Caveat> := if proof?(kind) then methods else {}
    let edges: Rel<Int, Int> := if proof?(kind) then premises else {}
    assume earlier_premises: earlier?(edges, k)
    assume premises_present: rests_on(edges, k) subset queries.before.domain

    call states := premise_verdicts(queries, k, kind, before, instances)
    call old_e := pass_evidence(own, states.unsettled_before, edges, k)
    call new_e := pass_evidence(own, states.unsettled_after, edges, k)
    -- Caveats are the same before and after: `pass_evidence` uses only
    -- `own` and `edges` for them, independently of the verdicts.
    let old_caveats: Set<Caveat> := caveats_of(old_e.random?, old_e.bounded?)
    let new_caveats: Set<Caveat> := caveats_of(new_e.random?, new_e.bounded?)
    call old := reported_pass(kind, before, own.image({k}), old_caveats, old_e.settled?)
    call new := reported_pass(
        kind,
        states.after,
        own.image({k}),
        new_caveats,
        new_e.settled?,
    )

    expect shown_kept: when old.shown != Verdict::Inconclusive,
        new.shown = old.shown and new.by_testing? = old.by_testing? and new.by_bound? = old.by_bound?
        and new.weakened? = old.weakened? and new.unsettled? = old.unsettled?
    expect decided_only_uncapped: when before != Verdict::Inconclusive and new.shown != old.shown,
        old.shown = Verdict::Inconclusive and old.unsettled? and new.shown = Verdict::Pass and not new.unsettled?
    expect caveats_kept: old_caveats = new_caveats
    expect passes_stay: when old.shown = Verdict::Pass, new.shown = Verdict::Pass
    expect failures_stay: when old.shown = Verdict::Fail, new.shown = Verdict::Fail
    expect only_undecided_changes: when new.shown != old.shown, old.shown = Verdict::Inconclusive
    expect new_verdict_from_query: when states.after != before,
        (instances = InstancesAnswer::Unsat and states.after = unsat_verdict(kind))
        or (induction_kind?(kind) and states.after = Verdict::Pass)
    expect lawless_kept: when not query_laws?(kind), states.after = before
    expect refuted_kept: when k in queries.refuted, states.after = before
    expect new_pass_reported: when states.after = Verdict::Pass,
        new.unsettled? = (not new_e.settled?) and new.weakened? = (new_e.settled? and new_caveats != own.image({k}))
}

-- The unchecked-axiom message depends on the own verdict and the module
-- model, separately from the evidence of the program's check premises.
-- Both checks compute their own verdict by the same `today_verdict`.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
expect laws_expansion(
    m: ModuleModel,
    n: ModuleSentence,
    kind: Kind,
    before: Verdict,
    instances: InstancesAnswer,
    refuted?,
    unfolding: Seq<RecPost>,
) {
    call v := today_verdict(kind, before, instances, refuted?, unfolding)
    call caveat := caveat_premise(m, n)
    call old_laws := law_premise(kind, before, caveat.laws?, asked_of?(m, n))
    call new_laws := law_premise(kind, v.after, caveat.laws?, asked_of?(m, n))

    expect caveats_kept: when before != Verdict::Inconclusive, new_laws.rests? = old_laws.rests?
    expect new_pass_caveat: when v.after = Verdict::Pass,
        new_laws.rests? = (caveat.laws? and query_laws?(kind) and from_unsat?(kind, Verdict::Pass)
        and not asked_of?(m, n))
}

-- A call's assumption check (0) becomes a pass. Its dependent claim (1)
-- already passed on its own, but now loses F0664 and is shown as a pass.
pub const SETTLING_QUERIES: Queries := Queries {
    kinds := {(0, Kind::InstanceAssumption), (1, Kind::Expectation)},
    before := {(0, Verdict::Inconclusive), (1, Verdict::Pass)},
    instances := {(0, InstancesAnswer::Unsat), (1, InstancesAnswer::Other)},
    refuted := {},
    unfolding := {},
}

set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
expect premise_becomes_settled() {
    call states := premise_verdicts(
        SETTLING_QUERIES,
        1,
        Kind::Expectation,
        Verdict::Pass,
        InstancesAnswer::Other,
    )
    call old_e := pass_evidence({}, states.unsettled_before, {(1, 0)}, 1)
    call new_e := pass_evidence({}, states.unsettled_after, {(1, 0)}, 1)
    call old := reported_pass(Kind::Expectation, Verdict::Pass, {}, {}, old_e.settled?)
    call new := reported_pass(Kind::Expectation, states.after, {}, {}, new_e.settled?)

    expect own_kept: states.after = Verdict::Pass
    expect previously_capped: old.shown = Verdict::Inconclusive and old.unsettled?
    expect now_shown: new.shown = Verdict::Pass and not new.unsettled?
}

-- The newly passing check itself leaves `unsettled`, since a check rests
-- on itself as well as its premises.
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "solver" in
expect own_pass_becomes_settled() {
    call states := premise_verdicts(
        SETTLING_QUERIES,
        0,
        Kind::InstanceAssumption,
        Verdict::Inconclusive,
        InstancesAnswer::Unsat,
    )
    call old_e := pass_evidence({}, states.unsettled_before, {}, 0)
    call new_e := pass_evidence({}, states.unsettled_after, {}, 0)
    call new := reported_pass(
        Kind::InstanceAssumption,
        states.after,
        {},
        {},
        new_e.settled?,
    )

    expect previously_unsettled: not old_e.settled?
    expect now_settled: new_e.settled? and new.shown = Verdict::Pass and not new.unsettled?
}
```

The Lean-hosted front end checks this chapter's items by name, since a
`#fren_check` without a path would check every earlier chapter again:

```fren
#fren_check today_verdict
#fren_check cover_ruled_out
#fren_check induction_not_for_witnesses
#fren_check realizability_unchanged
#fren_check premise_verdicts
#fren_check strict_expansion
#fren_check laws_expansion
#fren_check premise_becomes_settled
#fren_check own_pass_becomes_settled
```
