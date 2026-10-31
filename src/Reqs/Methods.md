# Proof methods

Fren settles each check by one of four *methods*:

- the **solver**, which proves the check's goal or finds a model;
- **enumeration**, which searches every behaviour up to a size
  ([Checking by enumeration](Check.md#checking-by-enumeration));
- **random** testing, which tries random behaviours
  ([Checking by testing](Check.md#checking-by-testing));
- **Lean**, a proof that the user writes. This method does not exist yet.

The source states each check's method with `set_option fren.evidence`.
Nothing falls back from one method to a weaker one by itself. Where the
method that the source sets does not run a check, an information message
says so (`F0654`). The one check that another method runs instead is the
solver's check of a value given where a subset type is declared, which
the solver runs whatever the evidence: that is stronger, not
weaker.

A method *decides* a check if it can both pass it and fail it. It is
*one-sided* if it can reach only one of those verdicts: it either
*refutes*, failing the check on a counterexample, or *confirms*, passing
it on a witness. Any other result of a one-sided method is
`Inconclusive`. A failed search never shows that no counterexample or
witness exists:

| Check | solver | enumerated | random | lean |
|---|---|---|---|---|
| realizability, expectations, call assumptions, determinism, definedness, completeness, disjointness, preconditions, postconditions | decides | decides up to the size | refutes | decides |
| cover goals, vacuity, redundancy, reachability | decides | decides up to the size | confirms | decides |

The first row's checks pass on a proof, and the second row's on a witness
(`check::proof?`; see [Verdict families](Check.md#verdict-families)). No
cell is a skip: every method can conclude something about every check.

One verdict outside a one-sided cell is allowed, and only for a single
method that the source chose. When the source sets `"random"` alone, a
check of the first row for which testing finds no counterexample passes,
reported as passing by random testing, with the caveat `Random` of the
chapter on evidence of #439. That is the trust level that the source
chose, never a silent upgrade (#446), and it is where that caveat arises
on such a check. In a combination of methods, such a pass counts for
nothing (see [Combinations](#combinations)). A witness that testing finds
for a check of the second row is genuine, so that pass has no caveat.

Random testing refutes realizability with an input for which no output
exists. Its goal has an `∃ outputs` within it, so an input for which the
search found no output is a counterexample only where the search saw
every output: where each output is defined from the input, or is of a
type with finitely many values, all of which the search tries
(`eval::test_verdict`). Elsewhere outputs may still exist, so testing
warns (`F0609`), and realizability is inconclusive.

Enumeration *decides up to the size*. Where it sees every behaviour, its
verdict is a decision. Elsewhere a model that it finds is still genuine,
but finding none is a decision only up to the size. For a check that
passes on a proof, that is a pass that holds up to the size, recorded as
such: bounded (`F0646`). For one that passes on a witness, it is
inconclusive (`check::enumerated_verdict`).

The rows cover every check that Fren runs:

- realizability includes the contract of an uninterpreted function
  ([Contracts](Check.md#contracts-of-uninterpreted-functions)), each type
  instance of a generic function's contract, and the assumptions of a
  global expectation;
- expectations include the obligations of a
  [refinement](Lang/Refinement.md), which are the expectations and call
  assumptions of a global expectation;
- definedness includes the values given where a subset type is declared
  ([Subset types](Check.md#subset-types));
- postconditions are those of a defined function, against its body.

`fren fix` asks the solver nothing yet. When conditional fixes do (#212),
a fix's equivalence will be an expectation, and will take that row.

```fren
pub mod check
```

## The matrix

`check::method_cell` states the table, over the kinds of check
(`check::Kind`) and the methods:

```fren
pub enum ProofMethod { Solver, Enumerated, Random, Lean }

-- What a method can conclude about a check.
pub enum Cell {
    Decides,           -- both verdicts
    DecidesUpToSize,   -- both where it sees every behaviour; elsewhere a model, or a pass up to the size
    Refutes,           -- only `Fail`, on a counterexample; chosen alone, also a pass with the caveat `Random` (#446)
    Confirms,          -- only `Pass`, on a witness
}

pub proc method_cell(kind: Kind, method: ProofMethod): (det cell: Cell) {
    use self::Cell::{Confirms, Decides, DecidesUpToSize, Refutes}

    ensure rule: cell = match method {
        ProofMethod::Solver | ProofMethod::Lean => Decides,
        ProofMethod::Enumerated => DecidesUpToSize,
        ProofMethod::Random => if proof?(kind) then Refutes else Confirms,
    }

    expect random_one_sided: when method = ProofMethod::Random, cell in {Refutes, Confirms}
    expect realizability_refuted: when method = ProofMethod::Random and kind = Kind::Realizability, cell = Refutes
}
```

The verdicts of enumeration and of testing are within their cells.
Enumeration fails a check that passes on a witness only where it sees
every behaviour, and a pass of one that passes on a proof is bounded
unless it does:

```fren
expect enumeration_within_matrix(
    kind: check::Kind,
    verdict: check::Verdict,
    conflict?,
    exact?,
    outputs_exact?,
) {
    use check
    call e := enumerated_verdict(kind, verdict, conflict?, exact?, outputs_exact?)
    call cell := method_cell(kind, check::ProofMethod::Enumerated)
    expect up_to_size: (cell.cell) = check::Cell::DecidesUpToSize
    expect witness_fails_exhausted: when not proof?(kind) and (e.reported) = check::Verdict::Fail, (exact?)
    expect proof_bounded: when proof?(kind) and (e.reported) = check::Verdict::Pass and not (exact?), (e.bounded?)
}
```

Random testing fails only checks of the row that it refutes:
`eval::random_within_matrix`, in [Evaluation](Eval.md#fren-quickcheck),
states it of `eval::test_verdict`.

## Combinations

A check may be set to a set of methods. They all run, and each
contributes what its cell allows: a counterexample from a method that
decides or refutes the check, a pass from one that decides or confirms
it, recorded as bounded if it holds only up to the size, and nothing
else. A one-sided method's other verdicts contribute nothing: a "no
counterexample found" from random testing never helps a check of the
first row pass. Then:

- the check fails if any method contributes a counterexample;
- otherwise it passes if any method contributes a pass, and the pass is
  bounded only if every pass contributed is;
- otherwise it is `Inconclusive`.

The pass's *method* is the strongest method that contributed a pass with
no caveat: Lean, then the solver, then enumeration, then random testing;
or enumeration, if every pass contributed is bounded, and then the pass
has the caveat `Bounded`. A check that does not pass has no method. A
witness that random testing finds, for a cover goal, vacuity, redundancy
or reachability, is a genuine witness, so its pass has no caveat: only a
pass of a check of the first row by random testing has the caveat
`Random`. Its *evidence*, in the sense of the chapter on
evidence of #439, is the weakest link: those caveats, with those of the
checks that it rests on. The summary records each method's verdict.

A single method is not a combination, and its report is its own: when
the source sets `"random"` alone, a check of the first row for which
testing finds no counterexample passes with the caveat `Random`, as
[The matrix](#the-matrix) allows. In a combination, the same verdict
contributes nothing, so a random pass is never counted there.

`check::combined` states this, over what each method reached: the
solver's answer to the check's query, what enumeration found, as for
`check::enumerated_verdict`, and the verdicts of testing and of a Lean
proof. The value of `fren.evidence` does not yet take a set (#447). Its
one combination today, `"enumerated+random"`, is enumeration with testing
beyond the bound, a single method whose answers are enumeration's (see
[Enumeration then testing](Check.md#enumeration-then-testing)):

```fren
-- What a method's verdict contributes to a combination: a counterexample,
-- a pass with no caveat, a pass up to the size, or nothing.
pub enum Contribution { Refuted, Passed, Bounded, Nothing }

-- What a verdict contributes, as the cell allows it.
pub fn contribution(cell: Cell, verdict: Verdict, bounded?): Contribution :=
    if verdict = Verdict::Fail and cell != Cell::Confirms then Contribution::Refuted
    else if verdict = Verdict::Pass and cell != Cell::Refutes then (if bounded? then Contribution::Bounded else Contribution::Passed)
    else Contribution::Nothing

pub proc combined(
    kind: Kind,
    selected: Set<ProofMethod>,
    solver: Outcome,             -- the solver's answer to the check's query
    enumerated: Verdict,         -- what the check algorithm reaches from enumeration's answers
    conflict?,                   -- as for `check::enumerated_verdict`
    exact?,
    outputs_exact?,
    random: Verdict,             -- the verdict of testing (`eval::test_verdict`)
    lean: Verdict,               -- what a Lean proof shows
): (det verdict: Verdict, det method: Option<ProofMethod>, det bounded?) {
    use self::Contribution::{Bounded, Nothing, Passed, Refuted}
    use self::ProofMethod::{Enumerated, Lean, Random, Solver}
    use self::Verdict::{Fail, Inconclusive, Pass}
    -- A single method's report is its own: chosen alone, random testing's
    -- pass of a check of the first row stands, with the caveat `Random` (#446).
    assume combination: exists (a: ProofMethod) (b: ProofMethod), a != b and a in selected and b in selected

    call by_proof := proved(solver)
    call by_witness := satisfiable(solver)
    call enumeration := enumerated_verdict(kind, enumerated, conflict?, exact?, outputs_exact?)
    call solver_cell := method_cell(kind, Solver)
    call enumerated_cell := method_cell(kind, Enumerated)
    call random_cell := method_cell(kind, Random)
    call lean_cell := method_cell(kind, Lean)
    -- What each selected method contributes, as its cell allows.
    let s: Contribution := if Solver in selected
        then contribution(
            solver_cell.cell,
            if proof?(kind) then by_proof.verdict else by_witness.verdict,
            false
        )
        else Nothing
    let e: Contribution := if Enumerated in selected
        then contribution(
            enumerated_cell.cell,
            enumeration.reported,
            enumeration.bounded?
        ) else Nothing
    let r: Contribution := if Random in selected then contribution(random_cell.cell, random, false) else Nothing
    let l: Contribution := if Lean in selected then contribution(lean_cell.cell, lean, false) else Nothing

    ensure refuted: (verdict = Fail) iff Refuted in {s, e, r, l}
    ensure passed: (verdict = Pass) iff (not Refuted in {s, e, r, l} and (Passed in {s, e, r, l} or Bounded in {
        s,
        e,
        r,
        l,
    }))
    ensure bound: bounded? iff (verdict = Pass and not Passed in {s, e, r, l})
    -- The strongest method that contributed a pass with no caveat, or
    -- enumeration's bounded pass; none unless the check passes.
    ensure strongest: method = (
        if verdict != Pass then Option::None
        else if l = Passed then Option::Some(Lean)
        else if s = Passed then Option::Some(Solver)
        else if e = Passed then Option::Some(Enumerated)
        else if r = Passed then Option::Some(Random)
        else Option::Some(Enumerated))

    expect ran: forall (m: ProofMethod), when method = Option::Some(m), m in selected
    expect only_passes: (method = Option::None) iff verdict != Pass
    expect every_bounded_pass: when proof?(kind) and Enumerated in selected and verdict = Pass
        and not Passed in {s, r, l} and not exact?, bounded?
    expect definedness_bounded: when selected = {Solver, Enumerated} and solver = Outcome::Unknown
        and kind = Kind::Definedness and enumerated = Pass and not exact?, verdict = Pass and bounded?

    expect any_refutes: when Random in selected and random = Fail and proof?(kind), verdict = Fail
    expect no_counterexample_adds_nothing: when selected = {Solver, Random} and solver = Outcome::Unknown
        and proof?(kind), verdict != Pass
    expect witness_confirms: when selected = {Solver, Random} and random = Pass and not proof?(kind)
        and solver = Outcome::Unknown, verdict = Pass and method = Option::Some(Random)
    expect bounded_passes: when selected = {Solver, Enumerated} and solver = Outcome::Unknown and proof?(kind)
        and enumerated = Pass and not exact?, verdict = Pass and bounded? and method = Option::Some(Enumerated)
    expect decided_unbounded: when selected = {Solver, Enumerated} and solver = Outcome::Unsat and proof?(kind)
        and enumerated = Pass, verdict = Pass and not bounded? and method = Option::Some(Solver)
    expect nothing_reached: when solver = Outcome::Unknown and enumerated = Inconclusive and random = Inconclusive
        and lean = Inconclusive, verdict = Inconclusive
}
```

Fren has no code that combines verdicts yet, so `combined` has no
`impl`. It will have one when `fren.evidence` takes sets (#447).

## What runs today

Not every cell of the table runs yet. `check::method_run` states what
Fren does today with a check of each kind, in each kind of item, set to
each method:

- the method *runs* it;
- the solver runs it instead, whatever the evidence;
- the method *skips* it, with a reason: nothing runs it, and an
  information message says so, with the reason (`F0654`);
- or the request is an error.

An error can also depend on what a check reads, not only on its kind.
Testing a check with an unbounded quantifier that has no domain is
`F0639`, and enumerating a procedure with a variable of a type that is
not enumerable is `F0645`. At the level of kinds and items, the errors
are these: before a function or a constant, whose checks are the
solver's, `fren.evidence` can be set to nothing but `"solver"` (`F0215`);
and `"lean"` is not yet a value of `fren.evidence` (`F0214`, whose note
says so).

Which checks random testing and enumeration run is `check::testable?`
and `check::enumerable?`, of [Checking by
testing](Check.md#checking-by-testing); `method_run` adds the items, the
values given where subset types are declared, and the reasons:

```fren
pub enum Dispatch {
    Run,         -- the method runs it
    BySolver,    -- the solver runs it instead
    Skip,        -- nothing runs it, and that is reported (`F0654`)
    Reject,      -- requesting the method is an error
}

-- Why a check runs as it does.
pub enum Reason {
    Selected,          -- the method that the evidence sets runs it
    NoLean,            -- Lean evidence is not yet a method: `"lean"` is `F0214`
    NotSettable,       -- only the solver can be set before a function or a constant: others are `F0215`
    SubsetType,        -- a value given where a subset type is declared is the solver's to check
    NoWitnessSearch,   -- testing searches for counterexamples, not for witnesses
    NoValue,           -- the check is about where the evaluator knows no value
    NotEnumerated,     -- enumeration does not enumerate indexes, nor a function's body
}

pub proc method_run(
    kind: Kind,
    item: CheckedItem,
    method: ProofMethod,     -- the method that the check's evidence sets
    obligation?,             -- a definedness check of a value given where a subset type is declared
): (det dispatch: Dispatch, det reason: Reason) {
    use self::Reason::{
        NoLean,
        NoValue,
        NoWitnessSearch,
        NotEnumerated,
        NotSettable,
        Selected,
        SubsetType,
    }
    assume obligation_definedness: when obligation?, kind = Kind::Definedness

    ensure reason_rule: reason = match method {
        ProofMethod::Solver => Selected,
        ProofMethod::Lean => NoLean,
        ProofMethod::Enumerated | ProofMethod::Random =>
            if item in {CheckedItem::Body, CheckedItem::Contract} then NotSettable
            else if obligation? then SubsetType
            else if method = ProofMethod::Enumerated then (if enumerable?(kind) then Selected else NotEnumerated)
            else if testable?(kind) then Selected
            else if proof?(kind) then NoValue
            else NoWitnessSearch,
    }
    ensure dispatch_rule: dispatch = match reason {
        Selected => Dispatch::Run,
        NoLean | NotSettable => Dispatch::Reject,
        SubsetType => Dispatch::BySolver,
        NoWitnessSearch | NoValue | NotEnumerated => Dispatch::Skip,
    }

    expect solver_runs_all: when method = ProofMethod::Solver, dispatch = Dispatch::Run
    expect lean_rejected: when method = ProofMethod::Lean, dispatch = Dispatch::Reject
    expect functions_solver_only: when item in {CheckedItem::Body, CheckedItem::Contract}
        and method != ProofMethod::Solver, dispatch = Dispatch::Reject
    expect realizability_tested: when method = ProofMethod::Random and kind = Kind::Realizability
        and item = CheckedItem::Component, dispatch = Dispatch::Run
}
```

The reasons for a skip are these:

- Random testing searches for a counterexample: a behaviour that meets
  the procedure, in which a constraint fails. It does not search for the
  witnesses that vacuity, redundancy and reachability need: a behaviour in
  which a trigger holds, one in which a constraint fails while the others
  hold, or one in which a case is taken. A test that reaches an
  expectation shows that its trigger can hold. But the trigger's vacuity
  check is not run, and testing that never reaches a trigger only warns
  (`F0612`). Enumeration runs these checks, and the message's help says
  so.
- Random testing does not run definedness, completeness, disjointness or
  preconditions either. Each is about where something has no value that
  the evaluator knows: an index out of range, a table or `match` where no
  case is taken, or an application that does not meet its preconditions.
  A test only reaches behaviours in which the constraints have values (see
  [Searching for behaviours](Eval.md#searching-for-behaviours)), so it
  can never find a counterexample.
- Enumeration does not run the definedness of indexes, which are of
  sequences, which it does not enumerate. Nor does it run the
  postconditions of a defined function: `fren.evidence` cannot be set for
  a function anyway.

The checks of a function or a constant, including a contract's
realizability and a body's postconditions, are always the solver's, so
setting another method before one is an error (`F0215`), rather than a
setting that sets nothing. The solver also checks a value given where a
subset type is declared, whatever the evidence: dropping that check
would leave a value outside its type unreported (`F0661`).

`check::method_run` is bound to `Fren.Core.dispatchOf`, which both front
ends consult for each dimension: for the checks to test, to enumerate and
to leave to the solver, including those of values given where subset
types are declared (`Fren.Core.Comp.untested`); for the reported skips
(`Fren.Core.Comp.skippedMsgs`); for whether a setting can be given before
a function or a constant (`Fren.Core.Evidence.settable`, `F0215`); and
for the note of `F0214` on `"lean"`.

### Today and the matrix

What runs today never claims more than the matrix allows. Enumeration
runs a check only where it decides up to the size, and random testing
only where it refutes or confirms:

```fren
expect today_within_matrix(kind: check::Kind, method: check::ProofMethod) {
    use check
    call today := method_run(kind, check::CheckedItem::Component, method, false)
    call cell := method_cell(kind, method)
    expect enumeration_up_to_size: when (today.dispatch) = check::Dispatch::Run
        and (method) = check::ProofMethod::Enumerated, (cell.cell) = check::Cell::DecidesUpToSize
    expect testing_one_sided: when (today.dispatch) = check::Dispatch::Run and (method) = check::ProofMethod::Random,
        (cell.cell) in {check::Cell::Refutes, check::Cell::Confirms}
}
```

Since no cell is a skip, every skip today is a gap to close, not a limit
of the method. The gaps between this section and the matrix are left to
later work on #368:

- random testing confirms vacuity, redundancy and reachability with
  witnesses, and refutes definedness, completeness, disjointness and
  preconditions (#443);
- enumeration decides the definedness of indexes, once sequences are
  enumerable, and postconditions (#444);
- `fren.evidence` can be set for functions and constants, rather than
  being `F0215` (#445);
- Lean evidence;
- `fren.evidence` takes sets of methods, combined by `check::combined`
  (#447).

`check::by_testing` and `check::by_evidence` follow `method_run`. They
skip a check exactly when `method_run` skips it under the method that
runs: enumeration if the evidence includes it, and otherwise testing; and
they leave a check to the solver exactly when `method_run` does:

```fren
expect by_evidence_follows(kind: check::Kind, tested?, enumerated?, obligation?) {
    use check
    assume obligation_definedness: when (obligation?), (kind) = check::Kind::Definedness
    call run := by_testing(kind, tested?)
    call chosen := by_evidence(kind, tested?, enumerated?, obligation?)
    call testing := method_run(
        kind,
        check::CheckedItem::Component,
        check::ProofMethod::Random,
        obligation?,
    )
    call testing_any := method_run(
        kind,
        check::CheckedItem::Component,
        check::ProofMethod::Random,
        false,
    )
    call enumeration := method_run(
        kind,
        check::CheckedItem::Component,
        check::ProofMethod::Enumerated,
        obligation?,
    )
    expect testing_run: when (tested?), ((run.run) = check::Run::Skipped)
        iff (testing_any.dispatch) = check::Dispatch::Skip
    expect enumeration_skips: when (enumerated?), ((chosen.method) = check::Method::Skipped)
        iff (enumeration.dispatch) = check::Dispatch::Skip
    expect testing_skips: when (tested?) and not (enumerated?), ((chosen.method) = check::Method::Skipped)
        iff (testing.dispatch) = check::Dispatch::Skip
    expect solver_instead: when (tested?) or (enumerated?), ((chosen.method) = check::Method::Solver)
        iff (testing.dispatch) = check::Dispatch::BySolver
}
```

## Solver queries

Every place that Fren asks the solver is a check of the table, a query
that a check asks to explain its result, or a proof about something
other than a check of the spec:

| Where | Check |
|---|---|
| `checkRealizable`, `checkRealizableUniversal` | realizability, of procedures, global expectations, contracts, and the type instances of generic contracts |
| `checkExpect`, `checkInst`, `checkCover`, `checkVacuity`, `checkRedundant`, `checkDeterminism` | expectations, call assumptions, cover goals, vacuity, redundancy, determinism |
| `checkDefinedness`, `checkTable`, `checkReach`, `checkPostcondition` | definedness and subset types, completeness, disjointness, preconditions, reachability, postconditions |
| `fren_recursive_case` (`Fren/RecursiveProof.lean`), in the theorems of a recursive function's postconditions (`Fren/View.lean`) | postconditions: the Lean proof by induction of what `checkPostcondition` checks, whose cases the solver closes; it is part of the function's checks, which only the solver runs (`F0215`) |
| `minimize`, `forces`, `forcesVariant`, `clashAt`, `branchConflictsOf`, more cover examples | none: they explain a result of the solver's, within its check |
| `consistent`, before redundancy | none: it decides whether redundancy is asked (`check::redundancy_asked`) |
| the evaluator's confirmation of a model (`Reqs/Eval#confirming-models`) | none: it checks a model of the solver's, and never gives a verdict of its own |
| `solverAnswer` (`Fren/Impl.lean`), for an `impl`'s obligation, and whether its assumptions never hold | none: it proves that an implementation meets a spec, not a check of the spec; `decide` and a written Lean proof are its other methods ([Proof](Impl.md#proof), [Vacuous implementations](Impl.md#vacuous-implementations)) |
| `solverAnswer`, for an interpretation's contract | none: it proves that an interpretation meets its type's constraint, with `decide` and a written Lean proof as its other methods ([Interpretations](Impl.md#interpretations)) |
| `fren mutate`'s search for equivalent mutants | none: it is about a mutant, not a check of the spec |

The shared check algorithms, `Fren.Core.checkComp`, run every check
with one backend per kind. The solver, enumeration and testing are such
backends, so a query that explains a result is asked of the method that
reached it.

```fren
#fren_check
```
