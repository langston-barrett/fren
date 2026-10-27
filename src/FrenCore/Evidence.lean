-- keep-sorted start
import FrenCore.Check
-- keep-sorted end

/-!
# Checking by testing (`Reqs/Check#checking-by-testing`)

Which checks a spec has tested rather than asked of the solver, as set by
`set_option fren.evidence "tested" in`, shared by both front ends. Each
front end drops these checks from the comp before `checkComp`, so that the
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

/-- The checks that testing cannot decide (`check::by_testing`). -/
def CheckKind.untestable (kind : CheckKind) : Bool :=
  kind == .vacuity || kind == .redundancy || kind == .definedness || kind == .completeness || kind == .disjointness
    || kind == .precondition || kind == .reachability

/-- How a check of kind `kind` is run, given whether its evidence is
testing (`check::by_testing`). Vacuity and redundancy ask whether
something can hold at all, which testing cannot decide; nor can it decide
definedness, completeness, disjointness or preconditions, which are about
where an expression is evaluated, where its value may be unknown. -/
def runOf (kind : CheckKind) (tested : Bool) : Run :=
  if !tested then .bySolver
  else if kind.untestable then .skipped
  else .byTesting

/-- The checks of a comp whose evidence is testing, or that are not run
because of it (`check::by_testing`). -/
structure Tested where
  realizable : Bool := false
  redundancy : Bool := false
  /-- Expectations and cover goals, whose checks are tested, and other
  constraints and definitions, whose vacuity and definedness are not run. -/
  props : Array Name := #[]
  /-- Instances: their assumptions, and the definedness of their bindings. -/
  insts : Array Name := #[]
  /-- `det out`s: their determinism. -/
  dets : Array Name := #[]
  deriving Inhabited

def Tested.any (t : Tested) : Bool :=
  t.realizable || t.redundancy || !t.props.isEmpty || !t.insts.isEmpty || !t.dets.isEmpty

/-- The checks set to testing by a comp's setting `all` and its members'
settings, each `none` if it has none: a member's setting takes precedence
(`Reqs/Check#checking-by-testing`). `constraints` are the comp's
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
    label? := some "not `\"solver\"`, `\"tested\"`, `\"enumerated\"` or `\"enumerated+tested\"`"
    notes := #["note: `\"tested\"` has the checks tested instead of asked of the solver, `\"enumerated\"` has them \
      decided by enumerating behaviours, smallest first, `\"enumerated+tested\"` tests them too where enumeration is not \
      complete, and `\"solver\"` is the default"] }

/-- `set_option fren.evidence` before something that has no checks it
could set. -/
def misplacedEvidenceMsg (what : String) : Msg :=
  { code? := some "F0215", headline := s!"`fren.evidence` cannot be set for {what}"
    label? := some "has no checks to test"
    notes := #["note: it can be set before a component, an expectation or global expectation, a cover goal, an instance or a `det out`"] }

/-- `set_option` before a member, of an option other than `fren.evidence`. -/
def memberOptionMsg (option : String) : Msg :=
  { code? := some "F0216", headline := s!"`{option}` cannot be set before a member"
    label? := some "not `fren.evidence`"
    notes := #["note: before a member, `set_option` sets only `fren.evidence`; other options are set before the component"] }

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
  | "tested" => some { tested := true }
  | "enumerated" => some { enumerated := true }
  | "enumerated+tested" => some { tested := true, enumerated := true }
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

end Fren.Core
