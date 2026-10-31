-- keep-sorted start
import FrenCore.Check
-- keep-sorted end

/-!
# Evidence (`Reqs/Check#checking-by-testing`, `Reqs/Evidence`)

Which checks a spec has tested rather than asked of the solver, as set by
`set_option fren.evidence "random" in`, shared by both front ends. Each
front end drops these checks from the procedure before `checkComp`, so that the
solver is asked nothing about them; the `fren` command then tests them.

And the evidence of a pass (`Reqs/Evidence`): which checks a check rests on
(`premisesOf`), its evidence from theirs (`passEvidence`), and how it is
reported (`reportedPass`).
-/

open Lean

namespace Fren.Core

/-- How a check is run (`check::Run`). -/
inductive Run where
  | bySolver
  | byTesting
  | skipped
  deriving Inhabited, BEq, DecidableEq, Repr

/-- A method that settles a check (`check::ProofMethod`). -/
inductive ProofMethod where
  | solver
  | enumerated
  | random
  | lean
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What Fren does with a check set to a method (`check::Dispatch`). -/
inductive Dispatch where
  /-- The method runs it. -/
  | run
  /-- The solver runs it instead, whatever the evidence. -/
  | bySolver
  /-- Nothing runs it, and that is reported (`F0654`). -/
  | skip
  /-- Requesting the method is an error. -/
  | reject
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Why a check runs as it does (`check::Reason`). -/
inductive Reason where
  /-- The method that the evidence sets runs it. -/
  | selected
  /-- Lean evidence is not yet a method: `"lean"` is `F0214`. -/
  | noLean
  /-- `fren.evidence` cannot set a method but the solver before a function
  or a constant: it is `F0215`. -/
  | notSettable
  /-- A value given where a subset type is declared is the solver's to check. -/
  | subsetType
  /-- Testing searches for counterexamples, not for witnesses. -/
  | noWitnessSearch
  /-- The check is about where the evaluator knows no value. -/
  | noValue
  /-- Enumeration does not enumerate indexes, nor a function's body. -/
  | notEnumerated
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether a pass of a check of this kind is a proof from hypotheses,
rather than a witness (`check::proof?`). -/
def CheckKind.proof (kind : CheckKind) : Bool :=
  !(kind == .cover || kind == .vacuity || kind == .reachability || kind == .redundancy)

/-- The checks that random testing runs (`check::testable?`). -/
def CheckKind.testable : CheckKind → Bool
  | .vacuity | .redundancy | .definedness | .completeness | .disjointness | .precondition | .reachability => false
  | _ => true

/-- The checks that enumeration runs (`check::enumerable?`): all but
definedness, of indexes, which only sequences have, and postconditions,
which only the bodies of functions have. -/
def CheckKind.enumerable : CheckKind → Bool
  | .definedness | .postcondition => false
  | _ => true

/-- What Fren does with a check of kind `kind` of an item `item` set to
`method`, and why (`check::method_run`). `obligation` is whether it is the
definedness of a value given where a subset type is declared. -/
def dispatchOf (kind : CheckKind) (item : CheckedItem) (method : ProofMethod) (obligation : Bool := false) :
    Dispatch × Reason :=
  let reason : Reason := match method with
    | .solver => .selected
    | .lean => .noLean
    | .enumerated | .random =>
      if item == .body || item == .contract then .notSettable
      else if obligation then .subsetType
      else if method == .enumerated then (if kind.enumerable then .selected else .notEnumerated)
      else if kind.testable then .selected
      else if kind.proof then .noValue
      else .noWitnessSearch
  let dispatch : Dispatch := match reason with
    | .selected => .run
    | .noLean | .notSettable => .reject
    | .subsetType => .bySolver
    | .noWitnessSearch | .noValue | .notEnumerated => .skip
  (dispatch, reason)

/-- The checks that testing cannot decide (`check::by_testing`): those
that `dispatchOf` skips under random testing. -/
def CheckKind.untestable (kind : CheckKind) : Bool :=
  (dispatchOf kind .component .random).1 == .skip

/-- Whether the solver checks a definedness check, whatever the evidence:
whether it is of a value given where a subset type is declared, `typed`
(`dispatchOf`). -/
def solverDefinedness (typed : Bool) : Bool :=
  [ProofMethod.random, .enumerated].all fun m => (dispatchOf .definedness .component m typed).1 == .bySolver

/-- How a check of kind `kind` is run, given whether its evidence is
testing (`check::by_testing`). Vacuity and redundancy ask whether
something can hold at all, which testing cannot decide; nor can it decide
definedness, completeness, disjointness or preconditions, which are about
where an expression is evaluated, where its value may be unknown. -/
def runOf (kind : CheckKind) (tested : Bool) : Run :=
  if !tested then .bySolver
  else if kind.untestable then .skipped
  else .byTesting

/-- The checks of a procedure whose evidence is testing, or that are not run
because of it (`check::by_testing`). -/
structure Tested where
  realizable : Bool := false
  redundancy : Bool := false
  /-- Expectations and cover goals, whose checks are tested, and other
  constraints and definitions, whose vacuity and definedness are not run. -/
  props : Array Name := #[]
  /-- Calls: their assumptions, and the definedness of their arguments. -/
  insts : Array Name := #[]
  /-- `det` variables: their determinism. -/
  dets : Array Name := #[]
  deriving Inhabited

def Tested.any (t : Tested) : Bool :=
  t.realizable || t.redundancy || !t.props.isEmpty || !t.insts.isEmpty || !t.dets.isEmpty

/-- The checks set to testing by a procedure's setting `all` and its members'
settings, each `none` if it has none: a member's setting takes precedence
(`Reqs/Check#checking-by-testing`). `constraints` are the procedure's
assumptions, requirements and definitions, and `expects` its expectations
and cover goals. -/
def Tested.ofSettings (all : Bool) (constraints : Array Name)
    (expects insts dets : Array (Name × Option Bool)) : Tested :=
  let pick (xs : Array (Name × Option Bool)) := xs.filterMap fun (n, s?) => if s?.getD all then some n else none
  { realizable := all, redundancy := all, props := (if all then constraints else #[]) ++ pick expects
    insts := pick insts, dets := pick dets }

/-- Whether the check `r` is one of `t`'s. -/
def Tested.covers (t : Tested) (r : CheckResult) : Bool :=
  match r.kind, r.prop? with
  | .realizable, _ => t.realizable
  | .redundancy, _ => t.redundancy
  | .expect, some n | .cover, some n | .vacuity, some n => t.props.contains n
  | .definedness, some n | .completeness, some n | .disjointness, some n | .precondition, some n
  | .reachability, some n =>
    t.props.contains n || t.insts.contains n
  | .inst, some n => t.insts.contains n
  | .determinism, some n => t.dets.contains n
  | _, _ => false

/-- The kind of check in prose, as the messages about skipped checks name it. -/
def CheckKind.noun : CheckKind → String
  | .realizable => "realizability"
  | .inst => "call assumption"
  | .expect => "expectation"
  | .cover => "cover"
  | .vacuity => "vacuity"
  | .redundancy => "redundancy"
  | .determinism => "determinism"
  | .definedness => "definedness"
  | .completeness => "completeness"
  | .disjointness => "disjointness"
  | .precondition => "precondition"
  | .postcondition => "postcondition"
  | .reachability => "reachability"

/-- The checks of kind `kind` of `c` that `t` sets, as the solver would ask
them, each as whether it is the definedness of a value given where a
subset type is declared: a constraint's vacuity, its redundancy, an
index's definedness, or a question about the cases of a table or a
`match`. -/
def Comp.checksOf (c : Comp F) (t : Tested) (kind : CheckKind) : Array Bool :=
  let mine (n : Name) := t.props.contains n || t.insts.contains n
  let one (b : Bool) : Array Bool := if b then #[false] else #[]
  match kind with
  | .realizable => one t.realizable
  | .redundancy => one (t.redundancy && !(c.assumes.isEmpty && c.reqs.isEmpty))
  | .expect => one (c.expects.any (t.props.contains ·.1))
  | .cover => one (c.covers.any (t.props.contains ·.1))
  | .vacuity => one (c.triggers.any (t.props.contains ·.1))
  | .inst => one (c.insts.any fun i => t.insts.contains i.name && !i.assumes.isEmpty)
  | .determinism => one (c.vars.any fun v => v.isDet && t.dets.contains v.name)
  | .definedness => c.indexes.filterMap fun s => if mine s.prop then some s.subsetTy?.isSome else none
  | .postcondition => #[]
  | k => one (c.tables.any fun s => s.goal.kind == k && mine s.site.prop)

/-- The kinds of `kinds` of the checks of `c` that `t` sets to `method`
and that `method` skips (`dispatchOf`), in the order of `kinds`, each with
why. -/
def Comp.skipped (c : Comp F) (t : Tested) (method : ProofMethod) (kinds : Array CheckKind) :
    Array (CheckKind × Reason) :=
  kinds.filterMap fun k =>
    ((c.checksOf t k).map (dispatchOf k .component method ·)).find? (·.1 == .skip) |>.map fun (_, why) => (k, why)

/-- The method in prose. -/
def ProofMethod.noun : ProofMethod → String
  | .solver => "the solver"
  | .enumerated => "enumeration"
  | .random => "random testing"
  | .lean => "Lean"

/-- `a`, `b` and `c`. -/
private def inProse (xs : Array String) : String :=
  match xs.toList.reverse with
  | last :: rest@(_ :: _) => s!"{", ".intercalate rest.reverse} and {last}"
  | _ => ", ".intercalate xs.toList

/-- The note that says why a method skips a check. -/
def Reason.note : Reason → String
  | .noWitnessSearch => "note: testing searches for counterexamples, not for witnesses: \
      a behaviour in which a trigger holds, a constraint fails while the others hold, or a case is taken"
  | .noValue => "note: where an index is out of range, no case of a table or `match` is taken, \
      or an application does not meet its preconditions, the evaluator knows no value, so no test reaches it"
  | .notEnumerated => "note: indexes are of sequences, which enumeration does not enumerate"
  | .noLean => "note: a Lean proof is not yet a method of `fren.evidence`"
  | .notSettable => "note: the checks of a function's body or contract, and of a constant's value, are the solver's"
  | .selected | .subsetType => ""

/-- The checks of `subject` of the kinds `skipped` that `method`, which
their evidence sets, does not run (`F0654`). The help names enumeration too
where it runs all of them (`dispatchOf`). -/
def skippedMsg (subject : String) (method : ProofMethod) (skipped : Array (CheckKind × Reason)) : Msg :=
  let reasons := skipped.foldl (init := #[]) fun acc (_, r) => if acc.contains r then acc else acc.push r
  let enumerated := method != .enumerated && skipped.all fun (k, _) => (dispatchOf k .component .enumerated).1 == .run
  { code? := some "F0654"
    headline := s!"the {inProse (skipped.map (·.1.noun))} checks of {subject} are not run by {method.noun}"
    notes := reasons.map (·.note) |>.push (if enumerated then
      "help: the solver and enumeration decide them: set `fren.evidence` to `\"solver\"` or `\"enumerated\"` to have them run"
      else "help: the solver decides them: set `fren.evidence` to `\"solver\"` to have them run") }

/-- `c` without the checks of `t`, and the kinds of check left to ask the
solver. -/
def Comp.untested (t : Tested) (c : Comp F) (kinds : Array CheckKind) : Comp F × Array CheckKind :=
  ({ c with
      expects := c.expects.filter (!t.props.contains ·.1)
      covers := c.covers.filter (!t.props.contains ·.1)
      triggers := c.triggers.filter (!t.props.contains ·.1)
      insts := c.insts.map fun i => if t.insts.contains i.name then { i with assumes := #[] } else i
      vars := c.vars.map fun v => if t.dets.contains v.name then { v with isDet := false } else v
      -- A value given where a subset type is declared is the solver's to
      -- check, whatever the evidence (`dispatchOf`).
      indexes := c.indexes.filter fun s =>
        solverDefinedness s.subsetTy?.isSome || (!t.props.contains s.prop && !t.insts.contains s.prop)
      tables := c.tables.filter fun s => !t.props.contains s.site.prop && !t.insts.contains s.site.prop },
    kinds.filter fun k => !(k == .realizable && t.realizable) && !(k == .redundancy && t.redundancy))

/-- `set_option fren.evidence` with a value that is not one of
`evidenceValues`. -/
def invalidEvidenceMsg (v : String) : Msg :=
  { code? := some "F0214", headline := s!"invalid evidence `{v}`"
    label? := some "not `\"solver\"`, `\"random\"`, `\"enumerated\"` or `\"enumerated+random\"`"
    notes := #["note: `\"random\"` has the checks tested on random behaviours instead of asked of the solver, \
      `\"enumerated\"` has them decided by enumerating behaviours, smallest first, `\"enumerated+random\"` tests them \
      too where enumeration is not complete, and `\"solver\"` is the default"] ++
      (if v == "tested" || v == "enumerated+tested" then
        #[s!"note: `\"tested\"` was renamed to `\"random\"`; write `\"{v.replace "tested" "random"}\"`"]
      -- Lean is a method, which runs no check yet (`dispatchOf`).
      else if v == "lean" then
        match dispatchOf .expect .component .lean with
        | (.reject, why) => #[why.note]
        | _ => #[]
      else #[]) }

/-- `set_option fren.evidence` before something that has no checks it
could set. -/
def misplacedEvidenceMsg (what : String) : Msg :=
  { code? := some "F0215", headline := s!"`fren.evidence` cannot be set for {what}"
    label? := some "has no checks to test"
    notes := #["note: it can be set before a procedure, an expectation or global expectation, a cover goal, a call or a `det` variable"] }

/-- `set_option fren.evidence "value" in` before an item, a function or a
constant, `what`, whose checks the setting cannot set (`dispatchOf`). -/
def itemEvidenceMsg (what value : String) : Msg :=
  { code? := some "F0215", headline := s!"`fren.evidence` cannot be set to `\"{value}\"` for {what}"
    label? := some "its checks are the solver's"
    notes := #[Reason.notSettable.note,
      "note: it can be set before a procedure, an expectation or global expectation, a cover goal, a call or a `det` variable"] }

/-- `set_option` before a member, of an option other than `fren.evidence`. -/
def memberOptionMsg (option : String) : Msg :=
  { code? := some "F0216", headline := s!"`{option}` cannot be set before a member"
    label? := some "not `fren.evidence`"
    notes := #["note: before a member, `set_option` sets only `fren.evidence`; other options are set before the procedure"] }

/-- The evidence of a check (`check::Evidence`): whether it is tested, and
whether it is enumerated; neither is the solver's. -/
structure Evidence where
  tested : Bool := false
  enumerated : Bool := false
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The methods that the evidence sets, but the solver. -/
def Evidence.methods (ev : Evidence) : List ProofMethod :=
  (if ev.enumerated then [.enumerated] else []) ++ (if ev.tested then [.random] else [])

/-- Whether the evidence `ev` can be set before an item, `item`: whether no
check of it rejects one of its methods (`dispatchOf`). Before a function
or a constant, only the solver can be set (`F0215`). -/
def Evidence.settable (ev : Evidence) (item : CheckedItem) : Bool :=
  ev.methods.all fun m => CheckKind.all.all fun k => (dispatchOf k item m).1 != .reject

/-- The value of `set_option fren.evidence`, or `none` if it is invalid
(`Reqs/Check#checking-by-enumeration`). -/
def evidenceOf? : String → Option Evidence
  | "solver" => some {}
  | "random" => some { tested := true }
  | "enumerated" => some { enumerated := true }
  | "enumerated+random" => some { tested := true, enumerated := true }
  | _ => none

/-- The value of `set_option fren.evidence`: whether it is testing, or
`none` if the value is invalid. -/
def evidenceTested? (v : String) : Option Bool := (evidenceOf? v).map (·.tested)

/-- The value of `set_option fren.evidence`: whether it is enumeration, or
`none` if the value is invalid. -/
def evidenceEnumerated? (v : String) : Option Bool := (evidenceOf? v).map (·.enumerated)

/-- The checks of both. -/
def Tested.inter (a b : Tested) : Tested :=
  { realizable := a.realizable && b.realizable, redundancy := a.redundancy && b.redundancy
    props := a.props.filter b.props.contains, insts := a.insts.filter b.insts.contains
    dets := a.dets.filter b.dets.contains }

/-- The checks of `a` but not of `b`. -/
def Tested.minus (a b : Tested) : Tested :=
  { realizable := a.realizable && !b.realizable, redundancy := a.redundancy && !b.redundancy
    props := a.props.filter (!b.props.contains ·), insts := a.insts.filter (!b.insts.contains ·)
    dets := a.dets.filter (!b.dets.contains ·) }

/-- The checks of either. -/
def Tested.union (a b : Tested) : Tested :=
  let merge (xs ys : Array Name) := ys.foldl (fun acc y => if acc.contains y then acc else acc.push y) xs
  { realizable := a.realizable || b.realizable, redundancy := a.redundancy || b.redundancy
    props := merge a.props b.props, insts := merge a.insts b.insts, dets := merge a.dets b.dets }

/-- The messages about the checks of `c`, shown as `subject`, of the kinds
`kinds`, that the method that their evidence sets does not run (`F0654`):
those set to random testing alone, then those set to enumeration. -/
def Comp.skippedMsgs (c : Comp F) (subject : String) (tested enumerated : Tested) (kinds : Array CheckKind) :
    Array Msg :=
  let one (t : Tested) (method : ProofMethod) : Array Msg :=
    let s := c.skipped t method kinds
    if s.isEmpty then #[] else #[skippedMsg subject method s]
  one (tested.minus enumerated) .random ++ one enumerated .enumerated

/-! ## The evidence of a pass (`Reqs/Evidence`) -/

/-- What a pass rests on besides a proof (`check::Caveat`). -/
inductive Caveat where
  /-- Random testing. -/
  | random
  /-- Enumeration up to a size bound. -/
  | bounded
  deriving Inhabited, DecidableEq, Repr

/-- A check, as the evidence of its pass sees it (`check::pass_evidence`):
the caveats of its own method, whether its own verdict is a pass, and the
positions of the earlier checks whose passes it takes as premises. -/
structure CheckEvidence (γ : Type) where
  own : List γ := []
  settled : Bool := true
  premises : List Nat := []
  deriving Inhabited

/-- `passEvidence`, after the checks whose evidence is `acc`. A premise
that is not an earlier check is not settled, so that it never strengthens
a pass. -/
def passEvidenceAux {γ : Type} [BEq γ] : List (CheckEvidence γ) → Array (List γ × Bool) → Array (List γ × Bool)
  | [], acc => acc
  | c :: cs, acc =>
    let ps := c.premises.filter (· < acc.size)
    passEvidenceAux cs (acc.push ((c.own ++ ps.flatMap (fun j => (acc[j]?.map (·.1)).getD [])).eraseDups,
      c.settled && c.premises.all (· < acc.size) && ps.all fun j => (acc[j]?.map (·.2)).getD true))

/-- The evidence of each of the checks `cs`, in order
(`check::pass_evidence`): its caveats, and whether it rests on no check
whose own verdict is not a pass. Each is its own, with the evidence of each
earlier check that it takes as a premise, which is computed before it, so
that it rests on what they rest on, transitively. -/
def passEvidence {γ : Type} [BEq γ] (cs : List (CheckEvidence γ)) : Array (List γ × Bool) := passEvidenceAux cs #[]

/-! ## The premises of a check (`Reqs/Evidence`) -/

/-- Where a check's query is, which decides its hypotheses
(`check::Site`). -/
inductive Site where
  /-- The procedure's realizability or a `det` output's determinism. -/
  | whole
  | assumption
  /-- A guarantee, expectation, cover goal or definition. -/
  | constraint
  /-- An argument of the call at this position. -/
  | callArgument (k : Nat)
  /-- An assumption of the call at this position. -/
  | callAssumption (k : Nat)
  /-- A clause or the body of the function at this position. -/
  | functionClause (f : Nat)
  | constant
  /-- The obligation of a refinement whose abstraction is the procedure at
  this position. -/
  | refinement (a : Nat)
  deriving Inhabited, DecidableEq, Repr

/-- What a function is to the facts of a query that applies it
(`check::FnKind`). -/
inductive FnKind where
  | contract
  /-- An instance of a generic function. -/
  | instance
  | recursive
  | defined
  deriving Inhabited, DecidableEq, Repr

/-- A check, as its premises see it (`check::CheckRecord`): what it runs
on, which says which checks the item has (`CheckedItem.kinds`,
`check::applies`); its kind; its site; the functions, or instances of
generic functions, whose facts its query has, by their positions, through
the unfolding of those that are defined and not recursive; and the subset
types whose invariants it brings. -/
structure CheckRecord where
  item : CheckedItem := .component
  kind : CheckKind
  site : Site
  applies : List Nat := []
  types : List Nat := []
  deriving Inhabited

/-- What a check may rest on, by position (`check::Premise`). -/
inductive Premise where
  /-- The realizability of the procedure that the item's call at this
  position calls. -/
  | realizability (j : Nat)
  /-- The assumption checks of the item's call at this position. -/
  | callAssumptions (j : Nat)
  /-- The item's own realizability. -/
  | ownRealizability
  /-- The realizability of the procedure at this position, a refinement's
  abstraction. -/
  | abstractionRealizability (a : Nat)
  | contractRealizability (f : Nat)
  /-- The check that decides the contract of the instance at this
  position. -/
  | instanceContract (i : Nat)
  /-- A recursive function's postcondition checks. -/
  | postconditions (f : Nat)
  /-- A subset type's inhabitation check. -/
  | inhabitation (t : Nat)
  deriving Inhabited, DecidableEq, Repr

/-- Whether the query of a check at `site` has the constraints of call `j`
among its hypotheses, of an item with `nCalls` calls
(`check::has_call?`). -/
def Site.hasCall (site : Site) (j nCalls : Nat) : Bool :=
  j < nCalls && match site with
    | .whole | .constraint | .refinement _ => true
    | .callArgument k | .callAssumption k => j < k
    | _ => false

/-- Whether the item has a realizability check of its own, which shows that
its assumptions and guarantees can hold together
(`check::own_realizability?`, `check::applies`). -/
def CheckedItem.ownRealizability (item : CheckedItem) : Bool := item.kinds.contains .realizable

/-- Whether the query of a check of kind `kind` at `site`, of the item
`item`, has the item's own assumptions and guarantees among its hypotheses,
and is not its realizability (`check::own_hypotheses?`). An item with no
realizability check of its own, such as a short-form global expectation, has
no such hypothesis, and nothing of it rests on a check that does not
exist. -/
def Site.ownHypotheses (site : Site) (item : CheckedItem) (kind : CheckKind) : Bool :=
  item.ownRealizability && kind != .realizable && match site with
    | .whole | .assumption | .constraint | .refinement _ => true
    | _ => false

/-- Whether the check at `site` is a clause of the function `f`
(`check::own_function?`). -/
def Site.ownFunction (site : Site) (f : Nat) : Bool :=
  match site with
  | .functionClause g => g == f
  | _ => false

/-- Whether the check `c` of an item with `nCalls` calls takes `p` as a
premise, where `kinds` says what each function is (`check::premise`). -/
def premised (c : CheckRecord) (nCalls : Nat) (kinds : List (Nat × FnKind)) (p : Premise) : Bool :=
  c.kind.proof && match p with
    | .realizability j | .callAssumptions j => c.site.hasCall j nCalls
    | .ownRealizability => c.site.ownHypotheses c.item c.kind
    | .abstractionRealizability a => c.site == .refinement a
    | .contractRealizability f => c.applies.contains f && kinds.contains (f, .contract) && !c.site.ownFunction f
    | .instanceContract i => c.applies.contains i && kinds.contains (i, .instance) && !c.site.ownFunction i
    | .postconditions f => c.applies.contains f && kinds.contains (f, .recursive) && !c.site.ownFunction f
    | .inhabitation t => c.types.contains t

/-- The premises of the check `c` (`check::premise`): each of those that
`premised` takes, in order. -/
def premisesOf (c : CheckRecord) (nCalls : Nat) (kinds : List (Nat × FnKind)) : List Premise :=
  ((List.range nCalls).flatMap (fun j => [Premise.realizability j, .callAssumptions j])
    ++ [Premise.ownRealizability]
    ++ (match c.site with | .refinement a => [Premise.abstractionRealizability a] | _ => [])
    ++ c.applies.flatMap (fun f => [Premise.contractRealizability f, .instanceContract f, .postconditions f])
    ++ c.types.map Premise.inhabitation)
    |>.filter (premised c nCalls kinds)

/-- How a check is reported, from its own verdict, the caveats of its own
method and its evidence (`check::reported_pass`). -/
structure ReportedPass where
  shown : Verdict
  /-- Counted among the passes by testing. -/
  byTesting : Bool
  /-- Counted among the passes by bounded enumeration. -/
  byBound : Bool
  /-- Weakened by a premise (`F0663`). -/
  weakened : Bool
  /-- Made inconclusive by a premise that is not settled (`F0664`). -/
  unsettled : Bool
  deriving Inhabited, DecidableEq, Repr

/-- How a check is reported (`check::reported_pass`). -/
def reportedPass (verdict : Verdict) (own caveats : List Caveat) (settled : Bool) : ReportedPass :=
  let shown := if verdict == .pass && !settled then .inconclusive else verdict
  let has (c : Caveat) := caveats.contains c
  { shown, byTesting := shown == .pass && has .random, byBound := shown == .pass && has .bounded
    weakened := shown == .pass && caveats.any (!own.contains ·)
    unsettled := verdict == .pass && !settled }

end Fren.Core
