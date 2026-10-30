-- keep-sorted start
import FrenCore.Check
-- keep-sorted end

/-!
# Checking by testing (`Reqs/Check#checking-by-testing`)

Which checks a spec has tested rather than asked of the solver, as set by
`set_option fren.evidence "random" in`, shared by both front ends. Each
front end drops these checks from the procedure before `checkComp`, so that the
solver is asked nothing about them; the `fren` command then tests them.
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
  /-- `fren.evidence` sets nothing before a function or a constant. -/
  | noSetting
  /-- A value given where a pattern type is declared is the solver's to check. -/
  | patternType
  /-- Testing searches for counterexamples, not for witnesses. -/
  | noWitnessSearch
  /-- The check is about where the evaluator knows no value. -/
  | noValue
  /-- Enumeration does not enumerate indexes, nor a function's body. -/
  | notEnumerated
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What Fren does with a check of kind `kind` of an item `item` set to
`method`, and why (`check::method_run`). `obligation` is whether it is the
definedness of a value given where a pattern type is declared. -/
def dispatchOf (kind : CheckKind) (item : CheckedItem) (method : ProofMethod) (obligation : Bool := false) :
    Dispatch × Reason :=
  let reason : Reason := match method with
    | .solver => .selected
    | .lean => .noLean
    | .enumerated | .random =>
      if item == .body || item == .contract then .noSetting
      else if obligation then .patternType
      else if method == .enumerated then
        if kind == .definedness || kind == .postcondition then .notEnumerated else .selected
      else if kind == .vacuity || kind == .redundancy || kind == .reachability then .noWitnessSearch
      else if kind == .definedness || kind == .completeness || kind == .disjointness || kind == .precondition then .noValue
      else .selected
  let dispatch : Dispatch := match reason with
    | .selected => .run
    | .noLean => .reject
    | .noSetting | .patternType => .bySolver
    | .noWitnessSearch | .noValue | .notEnumerated => .skip
  (dispatch, reason)

/-- The checks that testing cannot decide (`check::by_testing`): those
that `dispatchOf` skips under random testing. -/
def CheckKind.untestable (kind : CheckKind) : Bool :=
  (dispatchOf kind .component .random).1 == .skip

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

/-- Whether `c` has a check of kind `kind` among those that `t` sets, as
the solver would ask it: a constraint's vacuity, its redundancy, an index's
definedness, or a question about the cases of a table or a `match`. The
definedness of a value given where a pattern type is declared is not
counted: the solver checks it (`dispatchOf`). -/
def Comp.hasCheck (c : Comp F) (t : Tested) (kind : CheckKind) : Bool :=
  let mine (n : Name) := t.props.contains n || t.insts.contains n
  match kind with
  | .realizable => t.realizable
  | .redundancy => t.redundancy && !(c.assumes.isEmpty && c.reqs.isEmpty)
  | .expect => c.expects.any (t.props.contains ·.1)
  | .cover => c.covers.any (t.props.contains ·.1)
  | .vacuity => c.triggers.any (t.props.contains ·.1)
  | .inst => c.insts.any fun i => t.insts.contains i.name && !i.assumes.isEmpty
  | .determinism => c.vars.any fun v => v.isDet && t.dets.contains v.name
  | .definedness => c.indexes.any fun s => s.patTy?.isNone && mine s.prop
  | .postcondition => false
  | k => c.tables.any fun s => s.goal.kind == k && mine s.site.prop

/-- The kinds of `kinds` of the checks of `c` that `t` sets to `method`
and that `method` skips (`dispatchOf`), in the order of `kinds`, each with
why. -/
def Comp.skipped (c : Comp F) (t : Tested) (method : ProofMethod) (kinds : Array CheckKind) :
    Array (CheckKind × Reason) :=
  kinds.filterMap fun k =>
    let (d, why) := dispatchOf k .component method
    if d == .skip && c.hasCheck t k then some (k, why) else none

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
  | .selected | .noLean | .noSetting | .patternType => ""

/-- The checks of `subject` of the kinds `skipped` that `method`, which
their evidence sets, does not run (`F0654`). -/
def skippedMsg (subject : String) (method : ProofMethod) (skipped : Array (CheckKind × Reason)) : Msg :=
  let reasons := skipped.foldl (init := #[]) fun acc (_, r) => if acc.contains r then acc else acc.push r
  { code? := some "F0654"
    headline := s!"the {inProse (skipped.map (·.1.noun))} checks of {subject} are not run by {method.noun}"
    notes := reasons.map (·.note) |>.push "help: the solver decides them: set `fren.evidence` to `\"solver\"` to have them run" }

/-- `c` without the checks of `t`, and the kinds of check left to ask the
solver. -/
def Comp.untested (t : Tested) (c : Comp F) (kinds : Array CheckKind) : Comp F × Array CheckKind :=
  ({ c with
      expects := c.expects.filter (!t.props.contains ·.1)
      covers := c.covers.filter (!t.props.contains ·.1)
      triggers := c.triggers.filter (!t.props.contains ·.1)
      insts := c.insts.map fun i => if t.insts.contains i.name then { i with assumes := #[] } else i
      vars := c.vars.map fun v => if t.dets.contains v.name then { v with isDet := false } else v
      -- A value given where a pattern type is declared is the solver's to
      -- check, whatever the evidence (`check::by_evidence`).
      indexes := c.indexes.filter fun s => s.patTy?.isSome || (!t.props.contains s.prop && !t.insts.contains s.prop)
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
      else #[]) }

/-- `set_option fren.evidence` before something that has no checks it
could set. -/
def misplacedEvidenceMsg (what : String) : Msg :=
  { code? := some "F0215", headline := s!"`fren.evidence` cannot be set for {what}"
    label? := some "has no checks to test"
    notes := #["note: it can be set before a procedure, an expectation or global expectation, a cover goal, a call or a `det` variable"] }

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

end Fren.Core
