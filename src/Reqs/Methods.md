# Proof methods

Fren settles each check by one of four *methods*:

- the **solver**, which proves the check's goal or finds a model;
- **enumeration**, which searches every behaviour up to a size
  ([Checking by enumeration](Check.md#checking-by-enumeration));
- **random** testing, which tries random behaviours
  ([Checking by testing](Check.md#checking-by-testing));
- **Lean**, a proof that the user writes. This method does not exist yet.

The source states each check's method with `set_option fren.evidence`.
Nothing falls back from one method to another by itself.

A method *decides* a check if it can both pass it and fail it. It is
*one-sided* if it can reach only one of those verdicts: it either
*refutes*, failing the check on a counterexample, or *confirms*, passing
it on a witness. Any other result of a one-sided method is
`Inconclusive`. A failed search never shows that no counterexample or
witness exists:

| Check | solver | enumerated | random | lean |
|---|---|---|---|---|
| realizability | decides | decides up to the size | concludes nothing, so it is skipped | decides |
| expectations, call assumptions, determinism, definedness, completeness, disjointness, preconditions, postconditions | decides | decides up to the size | refutes | decides |
| cover goals, vacuity, redundancy, reachability | decides | decides up to the size | confirms | decides |

The second row's checks pass on a proof and the third row's on a witness
(see [Verdict families](Check.md#verdict-families)). Realizability is in
neither row, since its goal has an `∃ outputs` within it. A test that
finds no output for an input does not show that no output exists. And no
set of tests shows that every input has one.

Enumeration decides only up to the size. Where it has seen every
behaviour, its verdict is a decision. Elsewhere a model that it finds is
still genuine, but finding none is a decision only up to the size. For a
check that passes on a proof, that is a pass that holds *up to the size*,
reported as such (`F0646`). For one that passes on a witness, it is
inconclusive (`check::enumerated_verdict`).

The rows cover every check that Fren runs:

- realizability includes the contract of an uninterpreted function
  ([Contracts](Check.md#contracts-of-uninterpreted-functions)), each type
  instance of a generic function's contract, and the assumptions of a
  global expectation;
- expectations include the obligations of a
  [refinement](Lang/Refinement.md), which are the expectations and call
  assumptions of a global expectation;
- definedness includes the values given where a pattern type is declared
  ([Pattern types](Check.md#pattern-types));
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
    Decides,     -- both verdicts
    Refutes,     -- only `Fail`, on a counterexample
    Confirms,    -- only `Pass`, on a witness
    Skip,        -- neither: the method concludes nothing, and does not run it
}

-- Whether a check passes on a witness, a behaviour in which something
-- holds, rather than on a proof (`check::satisfiable`).
pub fn witnessed?(kind: Kind) := kind in {Kind::Cover, Kind::Vacuity, Kind::Redundancy, Kind::Reachability}

set_option fren.evidence "enumerated" in
pub proc method_cell(kind: Kind, method: ProofMethod): (det cell: Cell) {
    use self::Cell::{Confirms, Decides, Refutes, Skip}

    ensure rule: cell = match method {
        ProofMethod::Random => if witnessed?(kind) then Confirms else if kind = Kind::Realizability then Skip else Refutes,
        ProofMethod::Solver | ProofMethod::Enumerated | ProofMethod::Lean => Decides,
    }

    expect random_one_sided: when method = ProofMethod::Random, cell != Decides
    expect others_decide: when method != ProofMethod::Random, cell = Decides
}
```

## Combinations

A check may be set to a set of methods. They all run, and their
verdicts combine:

- the check fails if any method fails it;
- otherwise it passes if at least one method gives a *conclusive* pass:
  a pass by a method that decides the check, or a witness from one that
  confirms it, but not a pass up to the size where enumeration has not
  seen every behaviour;
- otherwise it is `Inconclusive`.

So a one-sided "no counterexample found" never makes a pass, nor does a
pass up to the size. The pass's evidence is the strongest method that
gave a conclusive pass: Lean, then the solver, then enumeration, then
random testing. The summary records each method's verdict.

`check::combined` states this, over what each selected method reached.
The value of `fren.evidence` does not yet take a set (#368). Its one
combination today, `"enumerated+random"`, is enumeration with testing
beyond the bound, a single method whose answers are enumeration's (see
[Enumeration then testing](Check.md#enumeration-then-testing)):

```fren
-- What one method reached for a check: its verdict, and whether a pass is
-- conclusive.
pub struct Reached { verdict: Verdict, conclusive? }

-- What the method `method` reached, of the four.
pub fn result_of(method: ProofMethod, solver: Reached, enumerated: Reached, random: Reached, lean: Reached): Reached :=
    match method {
    ProofMethod::Solver => solver,
    ProofMethod::Enumerated => enumerated,
    ProofMethod::Random => random,
    ProofMethod::Lean => lean,
}

pub proc combined(
    selected: Set<ProofMethod>,
    solver: Reached,
    enumerated: Reached,
    random: Reached,
    lean: Reached,
): (det verdict: Verdict, evidence: ProofMethod) {
    use self::ProofMethod::{Enumerated, Lean, Random, Solver}
    use self::Verdict::{Fail, Inconclusive, Pass}
    assume nonempty: selected != {}

    ensure refuted: (verdict = Fail) iff
        (exists (m: ProofMethod), m in selected and result_of(m, solver, enumerated, random, lean).verdict = Fail)
    ensure passed: (verdict = Pass) iff (verdict != Fail and (exists (m: ProofMethod), m in selected
        and result_of(m, solver, enumerated, random, lean).verdict = Pass
        and result_of(m, solver, enumerated, random, lean).conclusive?))
    -- The strongest method that gave a conclusive pass.
    ensure strongest: when verdict = Pass, evidence = (
        if Lean in selected and lean.verdict = Pass and lean.conclusive? then Lean
        else if Solver in selected and solver.verdict = Pass and solver.conclusive? then Solver
        else if Enumerated in selected and enumerated.verdict = Pass and enumerated.conclusive? then Enumerated
        else Random)

    expect any_refutes: when Random in selected and random.verdict = Fail, verdict = Fail
    expect one_sided_never_passes: when selected = {Random} and not random.conclusive?, verdict != Pass
    expect bounded_never_passes: when selected = {Enumerated, Random} and not enumerated.conclusive?
        and not random.conclusive?, verdict != Pass
    expect nothing_conclusive: when not solver.conclusive? and not enumerated.conclusive? and not random.conclusive?
        and not lean.conclusive? and verdict != Fail, verdict = Inconclusive
}
```

Fren has no code that combines verdicts yet, so `combined` has no
`impl`. It will have one when `fren.evidence` takes sets.

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
not enumerable is `F0645`. At the level of kinds, the only error is Lean
itself: `"lean"` is not yet a value of `fren.evidence`, so it is `F0214`.

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
    NoSetting,         -- `fren.evidence` sets nothing before a function or a constant
    PatternType,       -- a value given where a pattern type is declared is the solver's to check
    NoWitnessSearch,   -- testing searches for counterexamples, not for witnesses
    NoValue,           -- the check is about where the evaluator knows no value
    NotEnumerated,     -- enumeration does not enumerate indexes, nor a function's body
}

pub proc method_run(
    kind: Kind,
    item: CheckedItem,
    method: ProofMethod,     -- the method that the check's evidence sets
    obligation?,             -- a definedness check of a value given where a pattern type is declared
): (det dispatch: Dispatch, det reason: Reason) {
    use self::Kind::{
        Completeness,
        Definedness,
        Disjointness,
        Postcondition,
        Precondition,
        Reachability,
        Redundancy,
        Vacuity,
    }
    use self::Reason::{
        NoLean,
        NoSetting,
        NoValue,
        NoWitnessSearch,
        NotEnumerated,
        PatternType,
        Selected,
    }
    assume obligation_definedness: when obligation?, kind = Definedness

    ensure reason_rule: reason = match method {
        ProofMethod::Solver => Selected,
        ProofMethod::Lean => NoLean,
        ProofMethod::Enumerated => if item in {CheckedItem::Body, CheckedItem::Contract} then NoSetting
            else if obligation? then PatternType
            else if kind in {Definedness, Postcondition} then NotEnumerated
            else Selected,
        ProofMethod::Random => if item in {CheckedItem::Body, CheckedItem::Contract} then NoSetting
            else if obligation? then PatternType
            else if kind in {Vacuity, Redundancy, Reachability} then NoWitnessSearch
            else if kind in {Definedness, Completeness, Disjointness, Precondition} then NoValue
            else Selected,
    }
    ensure dispatch_rule: dispatch = match reason {
        Selected => Dispatch::Run,
        NoLean => Dispatch::Reject,
        NoSetting | PatternType => Dispatch::BySolver,
        NoWitnessSearch | NoValue | NotEnumerated => Dispatch::Skip,
    }

    expect solver_runs_all: when method = ProofMethod::Solver, dispatch = Dispatch::Run
    expect lean_rejected: when method = ProofMethod::Lean, dispatch = Dispatch::Reject
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
  (`F0612`).
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

`fren.evidence` sets nothing before a function or a constant (see
[Checking by testing](Check.md#checking-by-testing)), so their checks,
including a contract's realizability and a body's postconditions, are
always the solver's. The solver also checks a value given where a pattern
type is declared, whatever the evidence: dropping that check would leave
a value outside its type unreported (`F0661`).

`check::method_run` is bound to `Fren.Core.dispatchOf`. The front ends'
choices of which checks to test and to enumerate (`check::by_testing` and
`check::by_evidence`) are both made from it, and so are the reported
skips (`Fren.Core.Comp.skippedMsgs`).

### Today and the matrix

What runs today never claims more than the matrix allows. A method runs
a check only where the matrix gives it something to conclude, with one
exception, below. And every skip today is a gap to close, not a limit of
the method: the matrix has each skipped cell decide, refute or confirm.

```fren
expect today_within_matrix(kind: check::Kind, method: check::ProofMethod) {
    use check
    call today := method_run(kind, check::CheckedItem::Component, method, false)
    call cell := method_cell(kind, method)
    -- Random testing still runs realizability (see below).
    expect runs_conclude: when (today.dispatch) = check::Dispatch::Run and not ((kind) = check::Kind::Realizability
        and (method) = check::ProofMethod::Random), (cell.cell) != check::Cell::Skip
    expect skips_are_gaps: when (today.dispatch) = check::Dispatch::Skip, (cell.cell) != check::Cell::Skip
}
```

The exception is random testing, which still reports a pass where it
finds no counterexample. That pass is not conclusive. It rests on the
tests alone, and the summary counts it apart ("by random testing"; see
[Checking by testing](Check.md#checking-by-testing)). Realizability is
one such pass: testing concludes nothing about it, but it still runs, and
warns where it finds no output (`F0609`). By the matrix, all of these
would be `Inconclusive`, which would leave the checks that Fren's own
specs set to random testing unsettled. The gaps between this section and
the matrix are left to later work on #368:

- random testing confirms vacuity, redundancy and reachability with
  witnesses, and refutes definedness, completeness, disjointness and
  preconditions;
- enumeration decides the definedness of indexes, once sequences are
  enumerable, and postconditions;
- `fren.evidence` can be set for functions and constants;
- Lean evidence;
- whether a pass by random testing that is not conclusive stays a pass.

`check::by_evidence` follows `method_run`. It skips a check exactly when
`method_run` skips it under the method that runs: enumeration if the
evidence includes it, and otherwise testing:

```fren
expect by_evidence_follows(kind: check::Kind, tested?, enumerated?) {
    use check
    call chosen := by_evidence(kind, tested?, enumerated?, false)
    call testing := method_run(kind, check::CheckedItem::Component, check::ProofMethod::Random, false)
    call enumeration := method_run(kind, check::CheckedItem::Component, check::ProofMethod::Enumerated, false)
    expect enumeration_skips: when (enumerated?), (chosen.method) = check::Method::Skipped
        iff (enumeration.dispatch) = check::Dispatch::Skip
    expect testing_skips: when (tested?) and not (enumerated?), (chosen.method) = check::Method::Skipped
        iff (testing.dispatch) = check::Dispatch::Skip
}
```

## Solver queries

Every place that Fren asks the solver is a check of the table, or a
query that a check asks to explain its result:

| Where | Check |
|---|---|
| `checkRealizable`, `checkRealizableUniversal` | realizability, of procedures, global expectations, contracts, and the type instances of generic contracts |
| `checkExpect`, `checkInst`, `checkCover`, `checkVacuity`, `checkRedundant`, `checkDeterminism` | expectations, call assumptions, cover goals, vacuity, redundancy, determinism |
| `checkDefinedness`, `checkTable`, `checkReach`, `checkPostcondition` | definedness and pattern types, completeness, disjointness, preconditions, reachability, postconditions |
| `minimize`, `forces`, `clashAt`, `branchConflictsOf`, more cover examples | none: they explain a result of the solver's, within its check |
| `consistent`, before redundancy | none: it decides whether redundancy is asked (`check::redundancy_asked`) |
| the evaluator's confirmation of a model (`Reqs/Eval#confirming-models`) | none: it checks a model of the solver's, and never gives a verdict of its own |
| `fren mutate`'s search for equivalent mutants | none: it is about a mutant, not a check of the spec |

The shared check algorithms, `Fren.Core.checkComp`, run every check
with one backend per kind. The solver, enumeration and testing are such
backends, so a query that explains a result is asked of the method that
reached it.

```fren
#fren_check
```
