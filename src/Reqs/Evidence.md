# Evidence

A check's verdict says what Fren found. Its *evidence* says what that
verdict rests on, and how far it can be trusted. This chapter states it,
as part of what a pass means: Fren's soundness statement for the checks
of [Checks](Check.md).

A `Pass` from the solver, or from an enumeration that sees every
behaviour, is a proof: the property holds of every behaviour that the
spec allows. A `Pass` of a check whose pass is a proof (`check::proof?`,
in [Checks](Check.md#verdict-families)) from
[testing](Check.md#checking-by-testing), or from
[enumeration](Check.md#checking-by-enumeration) up to a size bound, is
weaker: no counterexample was found among the behaviours tried. These are
the two *caveats* of a pass: `Random`, for random testing, and `Bounded`.
They are about a check's evidence, set by `fren.evidence`, and are
separate from the trace levels of an implementation (`trusted`, `tested`,
solver, proved; see [Tracing](Trace.md)), which say how its code is shown
to meet a spec. A witness that random testing or enumeration finds, for a
cover goal, is a real witness, as the solver's would be, so a pass of a
check whose pass is a witness has no caveat, however it was found.

```fren
pub mod check
```

A pass that is a proof from hypotheses is only as good as its hypotheses.
A procedure's checks have among their hypotheses its own assumptions `A`,
guarantees `R` and definitions `D`, and its calls' constraints `I` (see
[Calls](Lang/Calls.md)). Each definition determines its variable, so `D`
can always hold. `A` and `R` can hold together at every admissible input
only where the procedure is realizable, which its own realizability check
shows, with its assumptions' satisfiability (`F0602`). A short-form global
expectation, `expect n: e`, has neither, and no realizability check
(`check::applies`), so its checks take no such hypothesis. A call's
constraints can hold only where its arguments meet the called procedure's
assumptions, which the call's [assumption
check](Check.md#call-assumptions) shows, and where the called procedure
has outputs, which its [realizability](Check.md#realizability) shows. If
either of those checks passed with a caveat, did not pass, or was not
run, `I` may be unsatisfiable at some admissible input, and every proof
from it holds there vacuously. In the same way, a query's facts `N` about an
application of an uninterpreted function with a
[contract](Lang/Items.md#contracts) can hold only where the contract is
realizable, and those about an application of a [recursive
function](Lang/Recursion.md#solver-encoding), its postconditions as ground
facts beside one step of its equations, only where its postconditions
hold, which their checks by induction show. And a variable, parameter,
existential output or uninterpreted application whose type is a [subset
type](Lang/SubsetTypes.md) brings the type's invariants as assumptions,
which can hold only where the type is inhabited, which its inhabitation
check (`F0660`) shows. The checks of a function's own clauses have its
preconditions among their hypotheses, which only the function's own
contract realizability (`F0632`) shows can hold. So:

- a check's evidence is the weakest of its own method's and of every check
  that it *rests on*: the checks whose passes it takes as premises, and
  theirs in turn, transitively; and
- a check that rests on one whose verdict is not a pass is not a pass
  either: it is `Inconclusive`.

Two examples, those of #414. `lookup` has no output at `1234567`, and
its realizability is only checked by random testing, so at best it passes
by random testing, with the caveat `Random`:

```text
mod demo

set_option fren.evidence "random" in
pub proc lookup(x: Int): (y: Int) {
    ensure r: y = 0 and x != 1234567
}

pub proc caller(x: Int): (z: Int) {
    assume a: x = 1234567
    call c := lookup(x)
    ensure q: z = c.y + 1
    expect wrong: z = 5
}

expect answers_one(x: Int) {
    assume a: x = 1234567
    call c := lookup(x)
    expect e: c.y = 1
}
```

At `x = 1234567`, `c`'s constraints are unsatisfiable, so the solver
proves `caller`'s realizability, `wrong`, and `e`, although `wrong` and
`e` are false and `caller` has no output at its only admissible input.
Each of these checks rests on `lookup`'s realizability, so each is at best
a pass by random testing, with at least the caveat `Random`. `caller`'s
realizability rests on it too, so a check that calls `caller` does as
well, and so does the realizability of `answers_one`, which a global
expectation with a block has (`check::applies`). Here random testing also
finds that `lookup` has no output at `1234567`, a literal of the spec, so
its realizability is `Inconclusive` (`F0609`), and `fren check` reports
each of the four as `Inconclusive`, with `F0664`:

```text
warning[F0664]: the realizability of `demo::caller` rests on the realizability of `demo::lookup`, which did not pass
warning[F0664]: `demo::caller::wrong` rests on the realizability of `demo::lookup`, which did not pass
warning[F0664]: the realizability of `demo::answers_one` rests on the realizability of `demo::lookup`, which did not pass
warning[F0664]: `demo::answers_one::e` rests on the realizability of `demo::lookup`, which did not pass
```

Where testing finds outputs at every input it tries, they are passes by
random testing instead, each with `F0663`. `check::issue_examples`, below,
checks both cases, and the ui test `test/ui/checks/evidence_premises.fren`
runs both through both front ends.

Realizability is a check whose pass is a proof: its pass is the solver's
proof that no input meets the assumptions without some outputs meeting the
guarantees, from `A` and `I`, and a counterexample would be such an input.
The rule applies to the checks whose passes are proofs: realizability,
expectations, call assumptions, determinism, definedness, completeness,
disjointness, preconditions, postconditions and the values given where
pattern types are declared. A `Pass` of a cover goal, of vacuity or of
reachability is a witness: a behaviour that meets the hypotheses, in which
something holds. Such a behaviour shows that the hypotheses can hold, so
the witness is genuine whatever the premises' evidence, and these checks
rest on nothing. The rule never changes a `Fail` either: a `Fail` is
already reported as a problem, so it needs no weaker evidence to be
noticed. A proof check's `Fail` is a counterexample, a model of the
hypotheses, which is genuine; a witness check's `Fail`, such as a cover
goal that cannot be met, can be vacuous for the reasons above, and is
still reported as one.

The checks are those of the whole program, in order: every file of a run
of `fren check`, in order, and every module that a Lean file imports,
then the file. Within an item, its calls' assumption checks come in the
calls' order, call `k`'s after those of every call `j < k`; then its own
realizability, which rests on them; then its other checks, which rest on
its realizability. Its calls' assumption checks, and the checks of its
calls' arguments, do not rest on its realizability, which rests on them:
they come before it. Their hypotheses are its assumptions and the earlier
calls, and where its assumptions cannot hold and its realizability check
is decided, that check fails (`F0602`) on the same item; where its
assumptions query answers `Unknown`, and the check is `Inconclusive`,
nothing caps them, and they can be vacuous passes. That gap is #487.
Within a function, its contract's realizability and its postcondition
checks come before what applies it, in the order in which the evidence is
computed, though both front ends report them after it; a subset type's inhabitation comes
before what uses the type. A procedure is declared before the procedures
that call it, and a function before what applies it, so a premise is
always an earlier check. A [generic
function](Lang/GenericFunctions.md)'s contract is checked once at its type
parameters, and each instance's contract, where that check does not pass,
with the first item whose checks apply it, before that item's checks. An
application of an instance rests on the check that decides the instance's
contract: the check at the type parameters, where it passed, and otherwise
the instance's own check, which comes before the first check that applies
the instance; an instance that no item applies has no check, and nothing
rests on it. The check at the type parameters is not otherwise a premise
of an instance: a contract that fails only at types that the spec does not
apply it at is accepted, as [Generic
functions](Lang/GenericFunctions.md) says. A premise names checks, which
each front end finds by their positions: `Realizability(j)` is the
realizability check of the procedure that the item's call `j` calls,
`CallAssumptions(j)` is call `j`'s assumption checks, one for each
assumption of the called procedure and for each of its parameters whose
type brings a constraint (`Lang/SubsetTypes`), `OwnRealizability` is the
item's own realizability check, with, for an expectation of a trait, its
vacuity under the laws (below), `AbstractionRealizability(a)` is the
realizability check of the abstraction of the item's refinement claim `a`,
by the claim's position among the item's refinement claims, `ContractRealizability(f)` is uninterpreted
function `f`'s contract's realizability check, `InstanceContract(i)` is
the check that decides instance `i`'s contract (above),
`Postconditions(f)` is recursive function `f`'s postcondition checks, one
for each postcondition, and `Inhabitation(t)` is subset type `t`'s
inhabitation check. That check is the realizability check
(`Kind::Realizability`, `Site::Whole`) of the type's declaration, which is
universal over the interpretations that the existing contracts admit
(`Lang/SubsetTypes`), so its record's `applies` lists the functions that
the type's invariants apply, and it rests on their contracts' checks in
turn. A check that rests on a premise that is not earlier, as none should,
is not settled, so that a mistake there never strengthens a pass.

Both front ends run every check that a check they run rests on, and keep
its evidence: `fren check` runs every check of the program, and
`#fren_check`, besides the items it names, runs the checks of every item
that one of those rests on, transitively, once, and keeps their evidence in
the environment, for the `#fren_check` commands after it and the modules
that import it. So a premise's evidence is never missing where a check that
rests on it is reported, and the two front ends find the same premises
settled (`check::runs_premises`).

An `impl`'s obligation rests on nothing: it has the calls' variables
existentially, with their constraints as conjuncts, not hypotheses, so it
shows that outputs exist rather than proving anything from the calls (see
[Implementations](Impl.md)). Its other hypotheses, the facts about the
uninterpreted functions that it applies and the invariants of its inputs'
subset types, hold too: an `impl` comes after an interpretation of each
abstract type and function (`Impl.md`, "Interpretations"), whose contract
and result type are proved in Lean (`Impl.md`, "Proving the obligation").
A contract's realizability takes no evidence setting, as a setting before
a function sets nothing, so it is a proof, and caps nothing, where it
passes; it can only be unsettled. Random testing chosen alone, as an
explicit evidence setting, passes a proof check with the caveat `Random`;
where methods are combined, random testing never makes a pass of a proof
check by itself, though a witness that it finds confirms a witness check's
pass.

Both front ends apply this rule to the premises that come from
procedures, refinement claims and the contracts of uninterpreted
functions: `Realizability(j)`, `CallAssumptions(j)`, `OwnRealizability`,
`AbstractionRealizability(a)` and `ContractRealizability(f)`
(`Fren.Core.itemEvidence`). Every check
of a refinement claim, its obligation and the definedness and cases of its
formulas, is at `Site::Refinement(a)`, where `a` is the claim's position
among the item's refinement claims (`Fren.Core.CheckResult.site`); the
definedness of the claim's arguments is among them, though its query does
not have the abstraction's calls, which is conservative. Both front ends
take the abstraction's realizability from the evidence that they keep for
procedures, as for a call's procedure. Each check's `applies` is recorded
by both front ends' query builders, from the facts that they give its
queries (`check::check_applies`, below), and each function's contract's
realizability is kept by the function's path. Both front ends check and
report the bodies and contracts of functions after the procedures and
global expectations, so they compute the contracts' evidence first, in
declaration order (`Fren.Core.contractsEvidence`), and `#fren_check` runs
the contracts of the functions that an item it names uses, as it runs the
procedures that the item calls. They do not apply the rule yet to
`InstanceContract`, `Postconditions` or `Inhabitation`, which need each
check to know which instances, recursive functions and subset types'
invariants its query has, as [Checks](Check.md#global-expectations) says
too; that is #522. Until then, a pass that rests only on one of those can be
vacuous where that check does not pass, as before.

## Resting on checks

`check::pass_evidence` states the evidence of a check, over the checks of
the program by their positions: the caveats of each check's own method, the
checks whose own verdict is not a pass, and the premises of each check. A
check rests on itself and on every check that its premises reach, through
the transitive closure of the premise relation. It is settled where none of
those is unsettled and each of their premises is earlier; where every
premise that it reaches is earlier, its caveats are theirs:

```fren
-- What a pass rests on besides a proof: random tests, or enumeration up
-- to a size bound.
pub enum Caveat { Random, Bounded }

-- The checks that check `k` rests on: itself, and every check that its
-- premises reach.
set_option fren.lint.undecidable "allow" in
pub fn rests_on(premises: Rel<Int, Int>, k: Int): Set<Int> := {k} union premises.closure.image({k})

-- Whether every premise of every check that `k` rests on is an earlier
-- check.
set_option fren.lint.undecidable "allow" in
pub fn earlier?(premises: Rel<Int, Int>, k: Int) :=
    forall (a: Int) (b: Int), when a in rests_on(premises, k) and (a, b) in premises, 0 <= b < a

set_option fren.lint.undecidable "allow" in
pub proc pass_evidence(
    own: Rel<Int, Caveat>,       -- the caveats of each check's own method, by the check's position
    unsettled: Set<Int>,         -- the checks whose own verdict is not a pass
    premises: Rel<Int, Int>,     -- each check, with the checks whose passes it takes as premises
    k: Int,                      -- the position of a check
): (random?, bounded?, det settled?) {
    -- Its caveats are those of every check that it rests on, where every
    -- premise that it reaches is earlier; elsewhere it is not settled, and
    -- its caveats are not pinned down.
    ensure random_rule: when earlier?(premises, k), random? iff Caveat::Random in own.image(rests_on(premises, k))
    ensure bounded_rule: when earlier?(premises, k), bounded? iff Caveat::Bounded in own.image(rests_on(premises, k))
    -- A premise that is not earlier fails closed.
    ensure settled_rule: settled? iff (rests_on(premises, k) inter unsettled = {} and earlier?(premises, k))

    -- No stronger than its own method, nor than any premise.
    expect own_random: when earlier?(premises, k) and (k, Caveat::Random) in own, random?
    expect premise_random: forall (j: Int), when earlier?(premises, k) and (k, j) in premises
        and (j, Caveat::Random) in own, random?
    expect premise_bounded: forall (j: Int), when earlier?(premises, k) and (k, j) in premises
        and (j, Caveat::Bounded) in own, bounded?
    expect premise_settled: forall (j: Int), when (k, j) in premises and j in unsettled, not settled?
    expect later_unsettled: forall (j: Int), when (k, j) in premises and j >= k, not settled?
}
```

`check::premise` computes which checks a check takes as premises, from
where its query is and what it applies. A check record gives the check's
kind; its *site*, which decides its query's hypotheses, as the tables of
[Checks](Check.md) and [Refinement](Lang/Refinement.md) do; and the
functions whose facts `N` its query has. Its query has a call's
constraints `I_j` among its hypotheses where [Checks](Check.md) says so: a
procedure's realizability and determinism, and the checks of a guarantee,
expectation, cover goal or definition, have every call's; an argument or
an assumption of a call has only the earlier calls'; an assumption has
none, nor does a function's clause or body, nor a constant's value. A
refinement's obligation, a `refines` claim of a global expectation block,
has the block's calls', and the meanings of its abstraction's own calls
(`Lang/Refinement`), which hold where the abstraction is realizable. Where
its query has `I_j`, the check takes as premises the realizability of the
procedure that call `j` calls, and call `j`'s assumption checks; a
refinement's obligation also takes its abstraction's realizability, which
rests on the abstraction's calls in turn. For each function whose facts
it has, it takes that function's contract's realizability, for an
uninterpreted function with a contract, or its postcondition checks, for a
recursive one; a defined function that is not recursive is unfolded, so it
brings the facts of what its body applies, and none of its own. A clause
of a function takes none of that function's own checks: they come before
them, and the postcondition checks of a recursive function take its
postconditions at its recursive applications as induction hypotheses, which
`lang::recursive_post_result` covers (below). A clause's hypotheses are the
function's preconditions, and only the function's own contract
realizability (`F0632`) shows that those can hold, so where that check does
not pass, or is `Inconclusive`, a clause check can be a vacuous pass that
nothing caps; a defined function has no realizability check at all
(`check::applies`). That gap is #487, beside #460. For each subset type
whose invariants its query brings, it takes the type's inhabitation check. A
check whose pass is a witness takes none. Read the other way round, every
hypothesis that a query has is backed by a premise that it takes, or needs
none: `check::has_hypothesis?` says which hypotheses a query has, over the
sorts of [Checks](Check.md), `check::backs` gives the premises that back
each, and `premise`'s `backed` states that `premise` takes every one of
them, so that no hypothesis goes unaccounted for. `backed` is only as
strong as `has_hypothesis?`, so `check::site_hypotheses` pins it from
below, row by row, from the tables of [Checks](Check.md) and
[Refinement](Lang/Refinement.md), stated apart from `premise`'s `rule`, so
that a `has_hypothesis?` that leaves a hypothesis out fails a named check
rather than emptying `backed`:

```fren
-- Where a check's query is, which decides its hypotheses (`Reqs/Check`,
-- `Reqs/Lang/Refinement`): the whole procedure, over `A`, `I` and `R`; an
-- assumption, over the other assumptions; a guarantee, expectation, cover
-- goal or definition, over `A`, `I` and `R`; an argument or an assumption of
-- the call at a position, over `A` and the earlier calls; a clause or the
-- body of the function at a position, over its preconditions; a constant's
-- value, over nothing; a check of the item's refinement claim at a
-- position, among its refinement claims, over the block's `A` and `I` and,
-- for its obligation and the formulas within it, the claim's abstraction's
-- calls. The definedness of the claim's arguments is put there too, though
-- its query does not have the abstraction's calls: that is conservative,
-- as it only adds the abstraction's realizability as a premise.
pub enum Site {
    Whole,
    Assumption,
    Constraint,
    CallArgument(Int),
    CallAssumption(Int),
    FunctionClause(Int),
    Constant,
    Refinement(Int),
}

-- What a function is to the facts of a query that applies it: uninterpreted
-- with a contract, an instance of a generic function, recursive, or defined
-- and not recursive, which is unfolded.
pub enum FnKind { Contract, Instance, Recursive, Defined }

-- A check: what it runs on, which says which checks the item has
-- (`check::applies`); its kind; its site; the functions, or instances of
-- generic functions, whose facts `N` its query has, by their positions,
-- through the unfolding of those that are defined and not recursive; and the
-- subset types whose invariants it brings.
pub struct CheckRecord {
    item: CheckedItem,
    kind: Kind,
    site: Site,
    applies: Set<Int>,
    types: Set<Int>,
}

-- What a check may rest on, by position: the realizability of the procedure
-- that the item's call at a position calls; that call's assumption checks;
-- the item's own realizability; the realizability of the abstraction of
-- the item's refinement claim at a position; an uninterpreted function's contract's realizability; the
-- check that decides an instance's contract; a recursive function's
-- postcondition checks; or a subset type's inhabitation.
pub enum Premise {
    Realizability(Int),
    CallAssumptions(Int),
    OwnRealizability,
    AbstractionRealizability(Int),
    ContractRealizability(Int),
    InstanceContract(Int),
    Postconditions(Int),
    Inhabitation(Int),
}

-- Whether the query of a check at `site` has the constraints of call `j`
-- among its hypotheses, of an item with `n_calls` calls.
pub fn has_call?(site: Site, j: Int, n_calls: Int) := 0 <= j < n_calls and match site {
    Site::Whole => true,
    Site::Constraint => true,
    Site::Refinement(_) => true,
    Site::CallArgument(k) => j < k,
    Site::CallAssumption(k) => j < k,
    _ => false,
}

-- Whether `p` is the assumption checks of the call whose assumption the
-- check at `site` is.
pub fn own_call?(site: Site, p: Premise) := match site {
    Site::CallAssumption(k) => p = Premise::CallAssumptions(k),
    _ => false,
}

-- Whether the item has a realizability check of its own, which shows that
-- its assumptions and guarantees can hold together, as `check::applies`
-- says. A short-form global expectation, `expect n: e`, has no assumptions,
-- so there is nothing to show and no check of it to rest on; a function's
-- body has none either, and its clauses rest on its contract's checks.
pub fn own_realizability?(item: CheckedItem) :=
    item in {
        CheckedItem::Component,
        CheckedItem::GlobalExpectation,
        CheckedItem::Contract,
    }

-- Whether the query of a check of this kind at `site`, of this item, has the
-- item's own assumptions among its hypotheses, with its guarantees where it
-- has both, and is not the realizability check that shows that they can
-- hold. An assumption's check is over the other assumptions, a subset of
-- `A`, which can hold wherever `A` can, so the item's realizability, which
-- shows that `A` can hold, shows that they can too. The converse fails:
-- without an assumption that contradicts the others, the rest can hold
-- where `A` cannot. So resting on it is conservative: an assumption's check
-- whose own hypotheses can hold is still capped where the item's
-- realizability does not pass.
pub fn own_hypotheses?(item: CheckedItem, kind: Kind, site: Site) := own_realizability?(item)
    and kind != Kind::Realizability
    and site is Site::Whole | Site::Assumption | Site::Constraint | Site::Refinement(_)

-- Whether the check at `site` is a clause of the function `f`.
pub fn own_function?(site: Site, f: Int) := match site {
    Site::FunctionClause(g) => g = f,
    _ => false,
}

-- A sort of hypothesis that a check's query can have (`Reqs/Check`): the
-- item's own assumptions, with its guarantees where it has both; its
-- definitions; the constraints of the call at a position; the facts `N` of
-- the function at a position that it applies; the invariants of the subset
-- type at a position; the preconditions of the function at a position, in a
-- clause of which the check is; and the calls of the abstraction of the
-- item's refinement claim at a position, of that claim's obligation. A guard `G`, which `Reqs/Check`
-- puts among the hypotheses of definedness, the values given where subset
-- types are declared, completeness, disjointness, reachability and
-- preconditions, is not one of these sorts: where it cannot hold, the
-- expression that it guards is never evaluated, so a vacuous pass there is
-- the intended answer, and an arm's reachability check reports a dead case.
pub enum Hypothesis {
    Assumptions,
    Definitions,
    Call(Int),
    Facts(Int),
    Invariants(Int),
    Preconditions(Int),
    Abstraction(Int),
}

-- Whether the query of the check `check`, of an item with `n_calls` calls,
-- has the hypothesis `h`.
pub fn has_hypothesis?(check: CheckRecord, h: Hypothesis, n_calls: Int) := match h {
    Hypothesis::Assumptions => own_realizability?(check.item)
        and not check.site is Site::FunctionClause(_) | Site::Constant,
    Hypothesis::Definitions => own_realizability?(check.item) and check.kind != Kind::Realizability
        and not check.site is Site::FunctionClause(_) | Site::Constant,
    Hypothesis::Call(j) => has_call?(check.site, j, n_calls),
    Hypothesis::Facts(f) => f in check.applies and not own_function?(check.site, f),
    Hypothesis::Invariants(t) => t in check.types,
    Hypothesis::Preconditions(f) => own_function?(check.site, f),
    Hypothesis::Abstraction(a) => check.site = Site::Refinement(a),
}

-- The premises that show that the hypothesis `h` of the check `check` can
-- hold. Every hypothesis that a query has is backed by one of these, which
-- `check::premise`'s `backed` states: it is the dual of `rule`, and it is
-- what says that no hypothesis goes unaccounted for. Four have none:
-- `Definitions`, because each definition determines its variable; the facts
-- of a function that `kinds` makes only defined, because a defined function
-- that is not recursive is unfolded, so its equations determine its value,
-- as definitions do, and `CheckRecord`'s `applies` never lists it anyway;
-- and the item's own assumptions at its calls' own checks, and a function's
-- preconditions in its own clauses, because the check that shows each can
-- hold comes after the checks that assume it, which #487 states. The
-- realizability check is itself the one that shows the item's own
-- assumptions can hold, so it rests on no check of its own.
pub fn backs(check: CheckRecord, h: Hypothesis, kinds: Rel<Int, FnKind>): Set<Premise> := match h {
    Hypothesis::Assumptions => if check.kind = Kind::Realizability
        or check.site is Site::CallArgument(_) | Site::CallAssumption(_)
        then {} else {Premise::OwnRealizability},
    Hypothesis::Definitions => {},
    Hypothesis::Call(j) => {Premise::Realizability(j), Premise::CallAssumptions(j)},
    Hypothesis::Facts(f) => (if (f, FnKind::Contract) in kinds then {Premise::ContractRealizability(f)} else {})
        union (if (f, FnKind::Instance) in kinds then {Premise::InstanceContract(f)} else {})
        union (if (f, FnKind::Recursive) in kinds then {Premise::Postconditions(f)} else {}),
    Hypothesis::Invariants(t) => {Premise::Inhabitation(t)},
    Hypothesis::Preconditions(_) => {},
    Hypothesis::Abstraction(a) => {Premise::AbstractionRealizability(a)},
}

set_option fren.lint.undecidable "allow" in
pub proc premise(
    check: CheckRecord,          -- the check
    n_calls: Int,                -- the number of the item's calls
    kinds: Rel<Int, FnKind>,     -- what each function is
    p: Premise,                  -- a check that it may rest on
): (det premised?) {
    ensure rule: premised? iff (proof?(check.kind) and match p {
        Premise::Realizability(j) => has_call?(check.site, j, n_calls),
        Premise::CallAssumptions(j) => has_call?(check.site, j, n_calls),
        Premise::OwnRealizability => own_hypotheses?(check.item, check.kind, check.site),
        Premise::AbstractionRealizability(a) => check.site = Site::Refinement(a),
        Premise::ContractRealizability(f) => f in check.applies and (f, FnKind::Contract) in kinds
            and not own_function?(check.site, f),
        Premise::InstanceContract(i) => i in check.applies and (i, FnKind::Instance) in kinds
            and not own_function?(check.site, i),
        Premise::Postconditions(f) => f in check.applies and (f, FnKind::Recursive) in kinds
            and not own_function?(check.site, f),
        Premise::Inhabitation(t) => t in check.types,
    })

    -- Every premise that backs a hypothesis of the query is one that the
    -- check takes: the dual of `rule`, over `check::backs`.
    expect backed: forall (h: Hypothesis), when proof?(check.kind)
        and has_hypothesis?(check, h, n_calls) and p in backs(check, h, kinds), premised?

    expect witnesses: when check.kind in {
        Kind::Cover,
        Kind::Vacuity,
        Kind::Reachability,
        Kind::Redundancy,
    },
        not premised?
    -- A procedure's checks over its own assumptions and guarantees rest on
    -- its realizability, but its calls' checks, which come before it, and its
    -- realizability itself do not.
    expect own_rests: when proof?(check.kind) and own_realizability?(check.item)
        and check.kind != Kind::Realizability and check.site = Site::Constraint
        and p = Premise::OwnRealizability, premised?
    -- An item with no realizability check of its own, such as a short-form
    -- global expectation, rests on none: there is no check to name.
    expect no_own_realizability: when not own_realizability?(check.item)
        and p = Premise::OwnRealizability, not premised?
    expect short_expectation_own: when check.item = CheckedItem::ShortExpectation
        and p = Premise::OwnRealizability, not premised?
    expect calls_before_own: when check.site is Site::CallArgument(_) | Site::CallAssumption(_)
        and p = Premise::OwnRealizability, not premised?
    expect own_not_self: when check.kind = Kind::Realizability and p = Premise::OwnRealizability, not premised?
    -- An application of an instance rests on the check that decides its
    -- contract.
    expect instance_rests: forall (i: Int), when proof?(check.kind) and check.applies = {i}
        and (i, FnKind::Instance) in kinds and not own_function?(check.site, i)
        and p = Premise::InstanceContract(i), premised?
    -- A subset type's invariants rest on its inhabitation.
    expect inhabitation_rests: forall (t: Int), when proof?(check.kind) and t in check.types
        and p = Premise::Inhabitation(t), premised?
    -- An application of one instance rests on no other instance's check.
    expect other_instance: forall (i: Int) (j: Int), when check.applies = {i} and i != j
        and p = Premise::ContractRealizability(j), not premised?
    -- A call's own assumptions are not among the hypotheses of their check.
    expect own_call: when own_call?(check.site, p), not premised?
    -- Nor are a function's own checks among those of its clauses.
    expect own_function: forall (f: Int), when own_function?(check.site, f)
        and p in {
            Premise::ContractRealizability(f),
            Premise::Postconditions(f),
        }, not premised?
    expect assumptions_alone: when check.site = Site::Assumption
        and p is Premise::Realizability(_) | Premise::CallAssumptions(_), not premised?
    -- Realizability's pass is a proof from `A` and `I`, so it rests on every
    -- call's callee.
    expect realizability_rests: when check.kind = Kind::Realizability and check.site = Site::Whole
        and n_calls > 0 and p = Premise::Realizability(0), premised?
    -- A refinement's obligation rests on its abstraction's realizability.
    expect refinement_rests: forall (a: Int), when proof?(check.kind) and check.site = Site::Refinement(a)
        and p = Premise::AbstractionRealizability(a), premised?
    -- A defined function that is not recursive brings no premise.
    expect defined_nothing: forall (f: Int), when (f, FnKind::Defined) in kinds and not (f, FnKind::Contract) in kinds
        and not (f, FnKind::Recursive) in kinds and p in {
            Premise::ContractRealizability(f),
            Premise::Postconditions(f),
        },
        not premised?
}

-- The hypotheses of each site, row by row from the tables of `Reqs/Check`
-- ("Realizability", "Global expectations", "Call assumptions" and the
-- "Where | Hypotheses" table of "Definedness") and `Reqs/Lang/Refinement`,
-- and from the meanings of `CheckRecord`'s `applies` and `types`. Each says
-- that `has_hypothesis?` has at least that hypothesis.
set_option fren.lint.undecidable "allow" in
expect site_hypotheses(check: CheckRecord, n_calls: Int, j: Int, f: Int, g: Int) {
    let procedure? := check.item in {CheckedItem::Component, CheckedItem::GlobalExpectation}
    let any_call? := 0 <= j < n_calls
    -- Realizability: `A` and `I`; `D` is substituted.
    expect whole: when procedure? and check.site = Site::Whole and any_call?,
        has_hypothesis?(check, Hypothesis::Assumptions, n_calls)
        and has_hypothesis?(check, Hypothesis::Call(j), n_calls)
    -- An assumption: the other assumptions.
    expect assumption: when procedure? and check.site = Site::Assumption,
        has_hypothesis?(check, Hypothesis::Assumptions, n_calls)
    -- A guarantee, expectation, cover goal or definition: `A`, `I` and `R`
    -- (a global expectation's `R` empty), and `D`.
    expect constraint: when procedure? and check.site = Site::Constraint and any_call?,
        has_hypothesis?(check, Hypothesis::Assumptions, n_calls)
        and has_hypothesis?(check, Hypothesis::Call(j), n_calls)
    expect constraint_definitions: when procedure? and check.site = Site::Constraint
        and check.kind != Kind::Realizability, has_hypothesis?(check, Hypothesis::Definitions, n_calls)
    -- An argument of call `k`, or an assumption of the procedure that it
    -- calls: `A`, `D` and the calls declared before it.
    expect call_argument: forall (k: Int), when procedure? and check.site = Site::CallArgument(k)
        and 0 <= j < k <= n_calls,
        has_hypothesis?(check, Hypothesis::Assumptions, n_calls)
        and has_hypothesis?(check, Hypothesis::Call(j), n_calls)
        and (when check.kind != Kind::Realizability, has_hypothesis?(check, Hypothesis::Definitions, n_calls))
    expect call_assumption: forall (k: Int), when procedure? and check.site = Site::CallAssumption(k)
        and 0 <= j < k <= n_calls,
        has_hypothesis?(check, Hypothesis::Assumptions, n_calls)
        and has_hypothesis?(check, Hypothesis::Call(j), n_calls)
        and (when check.kind != Kind::Realizability, has_hypothesis?(check, Hypothesis::Definitions, n_calls))
    -- A refinement's obligation: the block's `A` and `I`, and its
    -- abstraction's calls. The definedness of a claim's arguments is at this
    -- site too, conservatively, and its query does not have
    -- `Abstraction(a)`: this states only that `has_hypothesis?` has it, which
    -- makes such a check rest on more than it needs, never on less.
    expect refinement: forall (a: Int), when procedure? and check.site = Site::Refinement(a) and any_call?,
        has_hypothesis?(check, Hypothesis::Assumptions, n_calls)
        and has_hypothesis?(check, Hypothesis::Call(j), n_calls)
        and has_hypothesis?(check, Hypothesis::Abstraction(a), n_calls)
    -- A precondition, postcondition or the body of function `f`: its
    -- preconditions, whatever the kind of check.
    expect clause: when check.site = Site::FunctionClause(f),
        has_hypothesis?(check, Hypothesis::Preconditions(f), n_calls)
    -- Every query has the facts `N` of the functions that it applies: those
    -- of `f` itself in its own clauses are its induction hypotheses, which
    -- `lang::recursive_post_result` covers instead.
    expect facts: when f in check.applies and not check.site is Site::FunctionClause(_),
        has_hypothesis?(check, Hypothesis::Facts(f), n_calls)
    expect clause_facts: when check.site = Site::FunctionClause(g) and f != g and f in check.applies,
        has_hypothesis?(check, Hypothesis::Facts(f), n_calls)
    -- And the invariants of the subset types that it brings, at every site
    -- and of every kind.
    expect invariants: when f in check.types, has_hypothesis?(check, Hypothesis::Invariants(f), n_calls)
}
```

A refinement's abstraction is realizable for its admissible inputs, where
its calls' assumption checks hold too, so its calls' constraints can hold
there. A refinement introduces none of its abstraction's assumptions, so
where its block's assumptions allow an input that its abstraction does not
admit, its abstraction's calls may have no outputs there, whatever the
evidence: that is a question for [Refinement](Lang/Refinement.md), not for
evidence, and is #460; a fix for it that adds checks of the abstraction's
calls under the refinement's hypotheses makes them premises at
`Site::Refinement`, and so updates `check::premise` too.

Two of the facts that this chapter takes as inputs are computed elsewhere,
and are chained to the components that compute them. Whether an item has a
realizability check of its own is `check::applies`'s, and
`check::own_realizability_applies` says that the two agree, so that a
premise never names a check that the item does not have. The caveats of a
check's own method, `pass_evidence`'s `own`, are those of the method that
passed it, which `check::combined` gives; `check::own_caveats` states them
over that method, and `check::own_caveats_combined` chains the two into
`pass_evidence`, and `check::own_caveats_reported`, below, into
`check::reported_pass`. That chaining inherits `check::combined`'s
assumption that two or more methods are selected. A single method's report
is its own (`Reqs/Methods`): where `check::method_run` runs a check with
the one method that its evidence sets, `own_caveats`
takes that method, so a proof check that random testing alone passes, the
case of #414's example, has `Random`. That case is stated by `own_caveats`
alone, and `check::issue_examples` checks its consequences; no component
gives the method of a single-method pass to chain it to:

```fren
-- The caveats of a check's own method (`check::combined`): a pass by random
-- testing, which a combination never gives a proof check, and which an
-- evidence setting of `"random"` alone does (`Reqs/Methods`), has `Random`;
-- a pass that enumeration reached only up to the size bound has `Bounded`.
-- A check whose pass is a witness has neither, however it was found.
pub fn own_caveats(kind: Kind, method: Option<ProofMethod>, bounded?): Set<Caveat> :=
    if not proof?(kind) then {}
    else (if method = Option::Some(ProofMethod::Random) then {Caveat::Random} else {})
    union (if bounded? then {Caveat::Bounded} else {})

-- The caveats of the check at a position, as `check::pass_evidence` takes
-- them in `own`.
pub fn own_pairs(k: Int, caveats: Set<Caveat>): Rel<Int, Caveat> :=
    (if Caveat::Random in caveats then {(k, Caveat::Random)} else {})
    union (if Caveat::Bounded in caveats then {(k, Caveat::Bounded)} else {})

expect own_realizability_applies(item: CheckedItem) {
    call a := applies(item, Kind::Realizability)
    expect agrees: own_realizability?(item) iff a.runs?
}

set_option fren.lint.undecidable "allow" in
expect own_caveats_combined(
    kind: Kind,
    selected: Set<ProofMethod>,
    solver: Outcome,
    enumerated: Verdict,
    conflict?,
    exact?,
    outputs_exact?,
    random: Verdict,
    lean: Verdict,
    k: Int,
) {
    assume combination: exists (a: ProofMethod) (b: ProofMethod), a != b and a in selected and b in selected
    call c := combined(
        kind,
        selected,
        solver,
        enumerated,
        conflict?,
        exact?,
        outputs_exact?,
        random,
        lean,
    )
    -- A check that rests on nothing has exactly its own method's caveats.
    call e := pass_evidence(
        own_pairs(k, own_caveats(kind, c.method, c.bounded?)),
        {},
        {},
        k,
    )

    expect alone_random: e.random? iff Caveat::Random in own_caveats(kind, c.method, c.bounded?)
    expect alone_bounded: e.bounded? iff Caveat::Bounded in own_caveats(kind, c.method, c.bounded?)
    -- A combination never passes a proof check by random testing alone, so a
    -- pass of one has at most `Bounded`, and only where it is bounded.
    expect no_random: when proof?(kind), not Caveat::Random in own_caveats(kind, c.method, c.bounded?)
    expect bounded_iff: Caveat::Bounded in own_caveats(kind, c.method, c.bounded?) iff c.bounded?
    -- A witness check's pass has no caveat, as `check::reported_pass` assumes.
    expect witness_plain: when not proof?(kind), own_caveats(kind, c.method, c.bounded?) = {}
}
```

`check::item_premise` states which of those premises an item has, from
its structure, not from the results that a front end happens to have: the
realizability of the procedure that each call calls; each call's assumption
checks, where the called procedure has any, one for each of its assumptions
and for each of its inputs whose type brings a constraint, and the item runs
them (`check::applies`); the item's own realizability, where it has one; and
the realizability of the abstraction of each of its refinement claims, which
only a global expectation block has (`Lang/Refinement`); and the realizability
of the contract of each uninterpreted function whose contract its checks
apply (`check::check_applies`, below), by their positions, the item's own
function's first, which its own clauses do not rest on (`check::premise`'s
`own_function`).
A procedure that only checks that a subset type's invariants are defined
(`Lang/SubsetTypes`) runs no realizability check, so it has none to rest on.
Each premise that the item has is a check that its other checks rest on,
whether or not a front end has a result of it: where it has none, because
the method that its evidence sets did not run it (an enumeration that
stopped with an error, `F0644`, or testing whose results were dropped), that
check is among the unsettled ones of `check::pass_evidence`, so that a pass
that rests on it is `Inconclusive` (`F0664`, "which was not checked"),
never a proof:

```fren
pub proc item_premise(
    item: CheckedItem,           -- what the checks run on
    validator?,                  -- it only checks that a subset type's invariants are defined
    n_calls: Int,                -- the number of its calls
    assumed: Set<Int>,           -- the calls whose procedures have assumption checks
    n_abstractions: Int,         -- the number of its refinement claims
    n_functions: Int,            -- the number of the functions whose contracts its checks apply, its own among them
    p: Premise,                  -- a premise that a check of it may take
): (det has?) {
    ensure rule: has? iff match p {
        Premise::Realizability(j) => 0 <= j < n_calls,
        Premise::CallAssumptions(j) => 0 <= j < n_calls and j in assumed
            and item in {
                CheckedItem::Component,
                CheckedItem::GlobalExpectation,
                CheckedItem::ShortExpectation,
            },
        Premise::OwnRealizability => own_realizability?(item) and not validator?,
        Premise::AbstractionRealizability(a) => 0 <= a < n_abstractions,
        Premise::ContractRealizability(f) => 0 <= f < n_functions,
        _ => false,
    }
}

-- A call has no assumption checks to rest on where its procedure has none.
expect unassumed(
    item: CheckedItem,
    validator?,
    n_calls: Int,
    assumed: Set<Int>,
    n_abstractions: Int,
    n_functions: Int,
    j: Int,
) {
    assume none: not j in assumed
    call h := item_premise(
        item,
        validator?,
        n_calls,
        assumed,
        n_abstractions,
        n_functions,
        Premise::CallAssumptions(j),
    )
    expect absent: not h.has?
}

-- The items that have calls' assumption checks are those that run them.
expect call_assumptions_applies(item: CheckedItem) {
    call a := applies(item, Kind::InstanceAssumption)
    expect agrees: item in {
        CheckedItem::Component,
        CheckedItem::GlobalExpectation,
        CheckedItem::ShortExpectation,
    }
        iff a.runs?
}
```

`check::query_applies` states which functions' contracts the facts of a
check's query bring: those whose postconditions are among them. What a fact
is about is part of the fact (`Fren.Core.AppFact`), never read from its
name, which a postcondition shares with its clause, so a clause named
`nat` is a postcondition like any other:

```fren
-- What a fact that an application brings to a query is about: that the
-- application is at least 0, that it matches its result type, or a
-- postcondition of the function at a position.
pub enum Fact { AtLeastZero, ResultType, Postcondition(Int) }

pub proc query_applies(
    facts: Set<Fact>,            -- the facts of its query's applications
    f: Int,                      -- a function, by its position
): (det applied?) {
    ensure rule: applied? iff Fact::Postcondition(f) in facts
}
```

`check::query_facts` states which applications in a check's query bring
their facts to it, which is what `has_hypothesis?`'s `Facts` assumes: those
of every function but the one whose body or contract the check's item is.
Every query of such an item counts, not only those of its clauses' tables
and applications: the evidence puts each of its checks, its realizability
check among them, at `Site::FunctionClause` of that function
(`Fren.Core.CheckResult.site`). In an uninterpreted function's own
contract, each application of it is its value
([Contracts](Check.md#contracts-of-uninterpreted-functions)), so its facts
would be its own postconditions, which its realizability check is there to
show can hold, and among them the very clause that a check of
completeness, disjointness or reachability leaves out: with them,
`ensure e: table { x > 0 => r > 0, r < 0 => true, _ => true }` of `fn f(x:
Int): (r: Int)` would pass its disjointness, as the clause itself rules out
`x > 0 and r < 0`. A defined function's body is such an item too, but its
applications of itself bring nothing here anyway: a defined function has
no contract facts (`fnOf` names none), and a recursive one's postconditions
come in at its recursive applications through `recursiveQueryFacts`
instead (`lang::recursive_facts`). Both front ends' query builders decide
it with `Fren.Core.appBrings`, inside `Fren.Core.appFactsWith`, given the
item's function (`Comp.fn?`), so that one that left an application of the
function in its own clause would still not assume its contract there. That
holds of functions that are not generic: `f` is the function that `fnOf`
names, and it names none for an application of a generic function, whose
instance's premise is not applied yet (#522), so `query_facts` does not
cover a generic function's own contract, where only each front end's own
substitution of its value keeps its facts out:

```fren
pub proc query_facts(
    own_fn?,                     -- the check's item is the body or contract of a function
    g: Int,                      -- that function, by its position
    f: Int,                      -- the function of an application in its query, by its position
): (det brings?) {
    ensure rule: brings? iff not (own_fn? and f = g)

    -- What the query has is what the evidence takes it to have, for every
    -- kind of check of the item, its realizability among them.
    expect as_hypothesis: forall (item: CheckedItem) (kind: Kind), when own_fn?, brings? iff has_hypothesis?(
        CheckRecord {
            item,
            kind,
            site := Site::FunctionClause(g),
            applies := {f},
            types := {},
        },
        Hypothesis::Facts(f),
        0
    )
}
```

`check::check_applies` states which functions' contracts a check rests
on: those whose applications in its queries bring a postcondition as a
fact (`Fren.Core.appFactsWith`, which both front ends' query builders call,
and whose functions they record for each check, `Fren.Core.withApplies`),
or, for a check passed by random testing, which asks the solver nothing,
every function with a contract that its item applies: a test's
interpretation of such a function meets its postconditions where it can
(`Reqs/Eval`), and where they cannot hold it has no value, so no test there
finds a counterexample. Instances of generic functions and recursive
functions are left to `InstanceContract` and `Postconditions` (#522).
Where a front end runs the checks of a kind of an item together, as it runs
all of an item's call assumption checks, its redundancy checks and its
determinism checks, each of them is given the functions of all of their
queries (`Fren.Core.withAllApplies`), so `queried` is a superset of its
own. That is conservative: a function too many only adds a premise, which
can cap a pass but never strengthens one, and both front ends share it
through `Fren.Core.checkComp`. The ui test
`test/ui/checks/evidence_contracts.fren` pins it: the assumption check of
a call whose arguments apply no contract still rests on the contract that
a later call's arguments apply.

```fren
pub proc check_applies(
    queried: Set<Int>,           -- the functions whose postconditions its queries' facts have
    item_applies: Set<Int>,      -- the functions with contracts that its item applies
    random?,                     -- it was passed by random testing
): (det applies: Set<Int>) {
    out applies := if random? then item_applies else queried
}
```

`check::runs_premises` states that a front end that reports a check runs
every check that it rests on, so that the evidence of each is known where
it is reported:

```fren
set_option fren.lint.undecidable "allow" in
pub proc runs_premises(
    reported: Set<Int>,          -- the checks that a front end reports, by position
    premises: Rel<Int, Int>,     -- each check, with the checks whose passes it takes as premises
    k: Int,                      -- the position of a check
): (det run: Set<Int>) {
    out run := reported union premises.closure.image(reported)

    expect premises_run: when k in reported, rests_on(premises, k) subset run
}
```

The postcondition checks of a recursive function are by induction, with
the function's own postconditions as hypotheses at its recursive
applications (`lang::recursive_facts`), so they rest on each other;
`lang::recursive_post_result` is this rule within them: one of them is not
reported as a pass while another is unproved. That relation is cyclic, so
it stays apart from `check::pass_evidence`, whose premises are earlier
checks: from outside the function, its postcondition checks are one
premise, settled where all of them pass.

### The laws of a trait

A check of an [expectation of a trait](Lang/Traits.md#expectations) has
the trait's laws among the hypotheses of its queries, as it has the
contracts of the uninterpreted functions that its queries apply.
`check::query_hypotheses` states which hypotheses the queries of each kind
of check have: the laws, the item's assumptions and its calls. Every check
but realizability has all three. Realizability asks of the assumptions
alone, and then of the assumptions and calls, without the laws:

```fren
-- Whether the queries of a check of this kind have the laws.
pub fn query_laws?(kind: Kind) := kind != Kind::Realizability

pub proc query_hypotheses(kind: Kind): (det laws?) {
    ensure rule: laws? iff query_laws?(kind)

    expect realizability_alone: when kind = Kind::Realizability, not laws?
    expect expectations: when kind = Kind::Expectation, laws?
}
```

Where the laws cannot hold together with the item's assumptions and
calls, each query that has them is unsatisfiable, whatever else it asks.
So a verdict that comes from an `unsat` query rests on their holding
together: an expectation's pass, or a cover goal's failure. A verdict that
comes from a model does not, since the model meets them.

An item whose trait has laws, and that has assumptions or calls, has a
check of its own of this, its *vacuity under the laws*: whether the laws,
its assumptions and its calls can hold together, which a model shows. Its
checks rest on it as they rest on its realizability (`OwnRealizability`),
and so are reported as those are:

- Where it passes, no verdict rests on more than its proof.
- Where it fails, the assumptions and calls cannot hold with the laws
  (`F0602`). A pass of a proof check that rests on it is inconclusive
  (`F0664`), and a witness check's verdict stands, as where an item's
  assumptions cannot hold by themselves.
- Where it is not decided, which, with quantified laws, it seldom is, it
  is settled for the checks that rest on it. Each constraint whose verdict
  comes from an `unsat` query says, once, that it rests on the laws
  holding together with the assumptions and calls (`F0665`), and this
  check reports nothing of its own.

An item without assumptions or calls has no such check. Its verdicts rest
on the laws alone, whose consistency Fren does not check yet (#594), and
each constraint whose verdict comes from an `unsat` query says so
(`F0665`). `check::law_premise` states which verdicts carry `F0665`:

```fren
-- A pass of a check of this kind comes from an `unsat` query, not a
-- model: all but a cover goal's, a vacuity check's, a redundancy check's
-- and a reachability question's.
pub fn pass_from_unsat?(kind: Kind) := not kind in {
    Kind::Cover,
    Kind::Vacuity,
    Kind::Redundancy,
    Kind::Reachability,
}

-- The verdict comes from an `unsat` query.
pub fn from_unsat?(kind: Kind, verdict: Verdict) := match verdict {
    Verdict::Pass => pass_from_unsat?(kind),
    Verdict::Fail => not pass_from_unsat?(kind),
    Verdict::Inconclusive => false,
}

pub proc law_premise(
    kind: Kind,
    verdict: Verdict,
    laws?,
    asked?,                  -- the item has a vacuity under the laws
    lawful: Verdict,         -- its verdict, if it has one
): (det rests?) {
    ensure rule: rests? iff laws? and query_laws?(kind) and from_unsat?(kind, verdict)
        and (not asked? or lawful = Verdict::Inconclusive)

    expect lawless: when not laws?, not rests?
    expect counterexamples: when kind = Kind::Expectation and verdict = Verdict::Fail, not rests?
    expect alone: when laws? and kind = Kind::Expectation and verdict = Verdict::Pass and not asked?, rests?
    expect decided: when asked? and lawful != Verdict::Inconclusive, not rests?
}
```

## Reports

A check whose own verdict is `Pass` is reported as follows. Where it
rests on a check that is not settled, its verdict is `Inconclusive`, with
a warning (`F0664`) that names the check it rests on: "`wrong` rests on
the realizability of `lookup`, which did not pass". Otherwise it is a
pass. A pass whose caveats include `Random` is counted among the passes
by random testing in the summary, and one whose caveats include `Bounded` among
those by bounded enumeration. Where its caveats are more than its own
method's, it gets an information message (`F0663`) that names a check it
rests on, with that check's caveat: "`wrong` rests on the realizability
of `lookup`, which is only checked by random testing". Where that check's
own method does not have the caveat, but a check that it rests on does,
the message names that one too: "`top::good` rests on the realizability of
`mid`, which rests on the realizability of `echo`, which is only checked by
random testing".

`check::reported_pass` states it:

```fren
pub proc reported_pass(
    kind: Kind,                  -- the check's kind
    verdict: Verdict,            -- the check's own verdict
    own: Set<Caveat>,            -- the caveats of its own method
    caveats: Set<Caveat>,        -- its caveats, as `check::pass_evidence` gives them
    settled?,                    -- it rests on no check that is not settled
): (det shown: Verdict, det by_testing?, det by_bound?, det weakened?, det unsettled?) {
    assume own_within: own subset caveats
    -- A witness check's pass has no caveat, however it was found, and it
    -- rests on nothing.
    assume witness_plain: when not proof?(kind), own = {} and caveats = {}

    ensure verdict_rule: shown = (if verdict = Verdict::Pass and not settled? then Verdict::Inconclusive else verdict)
    ensure testing: by_testing? iff (shown = Verdict::Pass and Caveat::Random in caveats)
    ensure bound: by_bound? iff (shown = Verdict::Pass and Caveat::Bounded in caveats)
    -- `F0663`
    ensure weakened: weakened? iff (shown = Verdict::Pass and caveats != own)
    -- `F0664`
    ensure warned: unsettled? iff (verdict = Verdict::Pass and not settled?)

    expect fail_kept: when verdict = Verdict::Fail, shown = Verdict::Fail
    expect never_stronger: when shown = Verdict::Pass, settled?
    expect witness_unweakened: when not proof?(kind), not by_testing? and not by_bound? and not weakened?
}
```

`check::own_caveats_reported` chains the caveats of a check's own method,
from `check::combined`, through `check::pass_evidence` into `reported_pass`,
so that `reported_pass`'s assumptions `own_within` and `witness_plain` are
checked at a call rather than handed in. A check that rests on nothing is
shown with its own verdict, unweakened:

```fren
set_option fren.lint.undecidable "allow" in
expect own_caveats_reported(
    kind: Kind,
    selected: Set<ProofMethod>,
    solver: Outcome,
    enumerated: Verdict,
    conflict?,
    exact?,
    outputs_exact?,
    random: Verdict,
    lean: Verdict,
    k: Int,
) {
    assume combination: exists (a: ProofMethod) (b: ProofMethod), a != b and a in selected and b in selected
    call c := combined(
        kind,
        selected,
        solver,
        enumerated,
        conflict?,
        exact?,
        outputs_exact?,
        random,
        lean,
    )
    call e := pass_evidence(
        own_pairs(k, own_caveats(kind, c.method, c.bounded?)),
        {},
        {},
        k,
    )
    call r := reported_pass(
        kind,
        c.verdict,
        own_caveats(kind, c.method, c.bounded?),
        (if e.random? then {Caveat::Random} else {}) union (if e.bounded? then {Caveat::Bounded} else {}),
        e.settled?,
    )

    expect shown_own: r.shown = c.verdict and not r.weakened? and not r.unsettled?
    expect bound_own: r.by_bound? iff (c.verdict = Verdict::Pass
        and Caveat::Bounded in own_caveats(kind, c.method, c.bounded?))
}
```

## Lean

`#fren_check` runs no check set to random testing, and reports, as
information, that `fren check` runs them (see [Checking by
testing](Check.md#checking-by-testing)). A check that rests on one set to
random testing is treated the same way, with the same report: `#fren_check`
reports no verdict for it, as if it were set to random testing itself, and
says that `fren check` runs it. That is decided per check: a check that
rests on nothing set to random testing, such as the vacuity of an
expectation that does, is reported as usual. Which checks those are follows
from the evidence settings, the premises, and, for the checks that
`#fren_check` runs, whether their own verdict is `Fail`: a check that it
runs and that fails is reported all the same, as `fren check` reports it,
since no premise changes a `Fail` (`check::reported_pass`'s `fail_kept`).
So a value given where a subset type is declared, which the solver checks
whatever the evidence (`check::by_evidence`), is reported where it does not
hold, in a procedure set to random testing too. The settings and premises
are the same in both front ends, and the own verdicts of the checks not set
to random testing agree by the [agreement with
Lean](Cli.md#agreement-with-lean), so both front ends find the same checks
reported, and that agreement covers exactly the other checks, as it already
covers exactly the checks that are not set to random testing.
`check::hosted_runs` states it, from the evidence that
`check::pass_evidence` gives each check, where the checks set to random
testing are those whose own caveat is `Random`: the checks that Lean stands
for are read from the item's premises (`check::item_premise`), and both the
stand-ins and the decision are functions of `Fren.Core`
(`hostedStandIns`, `hostedReported`), not decided by the front end. Both front ends run enumeration, so a
premise decided by enumeration is settled in both, and one that
enumeration decides completely, over a finite domain, is a proof, which
caps nothing; one that it checks only up to the size bound has the caveat
`Bounded` in both. Every other premise is run by both front ends with the
solver (`check::runs_premises`), so they agree on whether it is settled,
and both report a check that rests on one that is not as `Inconclusive`,
with `F0664`.

```fren
set_option fren.lint.undecidable "allow" in
pub proc hosted_runs(
    own: Rel<Int, Caveat>,       -- the caveats of each check's own method, by the check's position
    failed: Set<Int>,            -- the checks whose own verdict is `Fail`
    premises: Rel<Int, Int>,     -- each check, with the checks whose passes it takes as premises
    k: Int,                      -- the position of a check
): (det reported?) {
    -- Its premises are earlier checks, as both front ends order them.
    assume in_order: earlier?(premises, k)

    -- Lean runs no check set to random testing, and stands for each that
    -- the item has as a premise with a pass whose own caveat is `Random`;
    -- no other check of Lean's has that caveat. So a check rests on one set
    -- to random testing just where `Random` is among the own caveats of the
    -- checks that it rests on.
    ensure rule: reported? iff (not Caveat::Random in own.image(rests_on(premises, k))
        or (k in failed and not (k, Caveat::Random) in own))

    expect own_setting: when (k, Caveat::Random) in own, not reported?
    expect failure_reported: when k in failed and not (k, Caveat::Random) in own, reported?
}
```

`check::issue_examples` checks the two examples above, with a procedure
`top` that calls `caller`, on their checks, whose premises it computes with
`check::premise`: procedure 0 is `lookup`, 1 `caller`, 2 `answers_one` and 3
`top`; check 0 is `lookup`'s realizability, 1 `caller`'s, 2 `wrong`, 3
`answers_one`'s realizability, which it has as a global expectation
(`check::applies`), 4 `e` and 5 `top`'s realizability. None of the calls'
procedures has an assumption, so they have no assumption checks:

```fren
-- The premise relation of the examples' checks, from whether each check
-- takes the realizability of the procedure that its call 0 calls: check 1
-- (`caller`'s realizability), 2 (`wrong`), 3 (`answers_one`'s
-- realizability) and 4 (`e`) through `lookup`'s, check 0, and check 5
-- (`top`'s realizability) through `caller`'s, check 1; and whether `wrong`
-- and `e` take their own item's realizability, checks 1 and 3.
pub fn example_edges(p1?, p2?, o2?, p3?, p4?, o4?, p5?): Rel<Int, Int> := (if p1? then {(1, 0)} else {})
    union (if p2? then {(2, 0)} else {}) union (if o2? then {(2, 1)} else {})
    union (if p3? then {(3, 0)} else {}) union (if p4? then {(4, 0)} else {})
    union (if o4? then {(4, 3)} else {}) union (if p5? then {(5, 1)} else {})

set_option fren.lint.undecidable "allow" in
set_option fren.lint.unrelated_binders "allow" in
expect issue_examples() {
    -- The premises, from the checks' records.
    call p1 := premise(
        CheckRecord {
            item := CheckedItem::Component,
            kind := Kind::Realizability,
            site := Site::Whole,
            applies := {},
            types := {},
        },
        1,
        {},
        Premise::Realizability(0),
    )
    call p2 := premise(
        CheckRecord {
            item := CheckedItem::Component,
            kind := Kind::Expectation,
            site := Site::Constraint,
            applies := {},
            types := {},
        },
        1,
        {},
        Premise::Realizability(0),
    )
    call o2 := premise(
        CheckRecord {
            item := CheckedItem::Component,
            kind := Kind::Expectation,
            site := Site::Constraint,
            applies := {},
            types := {},
        },
        1,
        {},
        Premise::OwnRealizability,
    )
    call p3 := premise(
        CheckRecord {
            item := CheckedItem::GlobalExpectation,
            kind := Kind::Realizability,
            site := Site::Whole,
            applies := {},
            types := {},
        },
        1,
        {},
        Premise::Realizability(0),
    )
    call p4 := premise(
        CheckRecord {
            item := CheckedItem::GlobalExpectation,
            kind := Kind::Expectation,
            site := Site::Constraint,
            applies := {},
            types := {},
        },
        1,
        {},
        Premise::Realizability(0),
    )
    call o4 := premise(
        CheckRecord {
            item := CheckedItem::GlobalExpectation,
            kind := Kind::Expectation,
            site := Site::Constraint,
            applies := {},
            types := {},
        },
        1,
        {},
        Premise::OwnRealizability,
    )
    call p5 := premise(
        CheckRecord {
            item := CheckedItem::Component,
            kind := Kind::Realizability,
            site := Site::Whole,
            applies := {},
            types := {},
        },
        1,
        {},
        Premise::Realizability(0),
    )
    let edges: Rel<Int, Int> := example_edges(
        p1.premised?,
        p2.premised?,
        o2.premised?,
        p3.premised?,
        p4.premised?,
        o4.premised?,
        p5.premised?
    )
    -- Where testing finds outputs at every input that it tries: each is a
    -- pass by random testing, `top`'s through `caller`'s.
    call e1 := pass_evidence({(0, Caveat::Random)}, {}, edges, 1)
    call e3 := pass_evidence({(0, Caveat::Random)}, {}, edges, 3)
    call e4 := pass_evidence({(0, Caveat::Random)}, {}, edges, 4)
    call e5 := pass_evidence({(0, Caveat::Random)}, {}, edges, 5)
    call r1 := reported_pass(
        Kind::Realizability,
        Verdict::Pass,
        {},
        if e1.random? then {Caveat::Random} else {},
        e1.settled?,
    )
    call r3 := reported_pass(
        Kind::Realizability,
        Verdict::Pass,
        {},
        if e3.random? then {Caveat::Random} else {},
        e3.settled?,
    )
    call r4 := reported_pass(
        Kind::Expectation,
        Verdict::Pass,
        {},
        if e4.random? then {Caveat::Random} else {},
        e4.settled?,
    )
    call r5 := reported_pass(
        Kind::Realizability,
        Verdict::Pass,
        {},
        if e5.random? then {Caveat::Random} else {},
        e5.settled?,
    )
    expect weakened: r1.weakened? and r1.by_testing? and r3.weakened? and r3.by_testing?
        and r4.weakened? and r4.by_testing?
        and r5.shown = Verdict::Pass and r5.weakened? and r5.by_testing?
    -- Where it finds an input without outputs, as it does here: each is
    -- inconclusive, `top`'s too.
    call u2 := pass_evidence({(0, Caveat::Random)}, {0}, edges, 2)
    call u4 := pass_evidence({(0, Caveat::Random)}, {0}, edges, 4)
    call u5 := pass_evidence({(0, Caveat::Random)}, {0}, edges, 5)
    call v2 := reported_pass(
        Kind::Expectation,
        Verdict::Pass,
        {},
        if u2.random? then {Caveat::Random} else {},
        u2.settled?,
    )
    call v4 := reported_pass(
        Kind::Expectation,
        Verdict::Pass,
        {},
        if u4.random? then {Caveat::Random} else {},
        u4.settled?,
    )
    call v5 := reported_pass(
        Kind::Realizability,
        Verdict::Pass,
        {},
        if u5.random? then {Caveat::Random} else {},
        u5.settled?,
    )
    expect inconclusive: v2.shown = Verdict::Inconclusive and v2.unsettled?
        and v4.shown = Verdict::Inconclusive and v4.unsettled?
        and v5.shown = Verdict::Inconclusive
}
```

```fren
#fren_check
```
