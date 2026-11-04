# Reports of modules

A spec whose items and clauses are all of today's forms keeps its
verdicts and messages under the design of #669, but for what the
instances of today's laws and induction by unfolding decide of a check
that today is Inconclusive. This chapter checks that guarantee, *strict
expansion*, over the model of [Implementations](Lang/Implementations.md).
Nothing in it takes a report as an input. It computes what a check of
today's forms is shown as, before and after, from its own verdict
(`lang::today_verdict`), the axioms that it rests on in the model
(`lang::caveat_premise`), and the rules that show every check:
[`check::reported_pass`](Evidence.md#reports) for its verdict, `F0663` and
`F0664`, and [`check::law_premise`](Evidence.md#the-laws-of-a-trait) for
`F0665`. It is a chapter of its own, after Evidence, since a chapter of the
language's module cannot call Evidence's requirements.

```fren
pub mod expansion
```

## Strict expansion

**Dynamic semantics**

r[module.expansion.computed] expansion::strict_expansion::{shown_kept, passes_stay, failures_stay, caveats_kept, only_undecided_changes}
Of a check of today's forms whose own verdict today is not Inconclusive,
everything that is shown is the same as today: its verdict, whether it is
counted among the passes by testing or by bound, `F0663`, `F0664` and
`F0665`. A pass stays a pass, and a failure a failure.

r[module.expansion.induction] expansion::strict_expansion::{new_pass_reported, new_pass_caveat}
A check of today's forms that today is Inconclusive may pass, by the
instances of today's laws or by induction by unfolding
([Recursion](Lang/Recursion.md), #750). The new pass is reported as every
pass is, by `check::reported_pass`: it is shown as Inconclusive, with
`F0664`, where it rests on a check that is not settled, and gets `F0663`
where its caveats are more than its own method's. It carries `F0665`
exactly where `check::law_premise` gives it, from the axioms that it rests
on in the model.

r[module.expansion.corpus]
Each stage of #669 that lands compares the messages of Fren's own specs
and of the ui tests, before and after, and every difference is one that
strict expansion allows.

```fren
use check::{Caveat, Kind, Verdict, from_unsat?, law_premise, proof?, query_laws?, reported_pass}

use lang::{
    InstancesAnswer,
    ModuleModel,
    ModuleSentence,
    TodayVerdict,
    caveat_premise,
    today_verdict,
}

-- A check's verdict, as Evidence takes it.
pub fn evidence_verdict(v: TodayVerdict): Verdict := match v {
    TodayVerdict::Pass => Verdict::Pass,
    TodayVerdict::Fail => Verdict::Fail,
    TodayVerdict::Inconclusive => Verdict::Inconclusive,
}

-- What is shown of a check.
pub struct ShownReport {
    shown: Verdict,
    by_testing?,
    by_bound?,
    weakened?,       -- `F0663`
    unsettled?,      -- `F0664`
    laws?,           -- `F0665`
}

set_option fren.lint.undecidable "allow" in
-- Of every check of every model, and so of every check of today's forms.
expect strict_expansion(
    m: ModuleModel,
    n: ModuleSentence,         -- the check
    kind: Kind,               -- its kind
    before: TodayVerdict,      -- its own verdict today, with today's laws quantified
    instances: InstancesAnswer,
    vacuity?,
    induction?,
    asked?,
    own: Set<Caveat>,         -- the caveats of its own method, the same before and after
    caveats: Set<Caveat>,     -- its caveats, which the checks it rests on give, the same before and after
    settled?,                        -- it rests on no check that is not settled, before and after
) {
    -- A model of today's query meets the quantified laws, and so their
    -- instances.
    assume sound: not (before = TodayVerdict::Fail and instances = InstancesAnswer::Unsat)
    assume own_within: own subset caveats
    assume witness_plain: when not proof?(kind), own = {} and caveats = {}
    assume vacuity_kind: vacuity? iff kind = Kind::Vacuity

    call v := today_verdict(m, n, before, instances, vacuity?, induction?, asked?)
    call caveat := caveat_premise(m, n)
    call old := reported_pass(kind, evidence_verdict(before), own, caveats, settled?)
    call new := reported_pass(kind, evidence_verdict(v.after), own, caveats, settled?)
    call old_laws := law_premise(kind, evidence_verdict(before), caveat.laws?, asked?)
    call new_laws := law_premise(kind, evidence_verdict(v.after), caveat.laws?, asked?)

    expect shown_kept: when before != TodayVerdict::Inconclusive,
        new.shown = old.shown and new.by_testing? = old.by_testing? and new.by_bound? = old.by_bound?
        and new.weakened? = old.weakened? and new.unsettled? = old.unsettled?
    expect caveats_kept: when before != TodayVerdict::Inconclusive, new_laws.rests? = old_laws.rests?
    expect passes_stay: when old.shown = Verdict::Pass, new.shown = Verdict::Pass
    expect failures_stay: when old.shown = Verdict::Fail, new.shown = Verdict::Fail
    expect only_undecided_changes: when new.shown != old.shown, old.shown = Verdict::Inconclusive
    expect new_pass_reported: when before = TodayVerdict::Inconclusive and v.after = TodayVerdict::Pass,
        new.unsettled? = (not settled?) and new.weakened? = (settled? and caveats != own)
    expect new_pass_caveat: when before = TodayVerdict::Inconclusive and v.after = TodayVerdict::Pass,
        new_laws.rests? = (caveat.laws? and query_laws?(kind) and from_unsat?(kind, Verdict::Pass)
        and not asked?)
}
```

The Lean-hosted front end checks this chapter's items by name:

```fren
#fren_check strict_expansion
```
