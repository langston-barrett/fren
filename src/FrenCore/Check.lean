-- keep-sorted start
import FrenCore.Diagnostic
import FrenCore.Names
import Lean.Data.Name
-- keep-sorted end

/-!
# Checks

The check algorithms and verdicts (`Reqs/Check`), shared by the Lean-hosted
front end and the standalone binary. They are generic over a solver
`Backend`: formulas `F` (Lean terms, or SMT-LIB text) and model values `V`.

Every query asks whether a goal can be proved from hypotheses: `unsat` means
"follows", and `sat` comes with a model.
-/

open Lean

namespace Fren.Core

inductive CheckKind where
  | realizable
  | inst
  | expect
  | cover
  | vacuity
  | redundancy
  | determinism
  | definedness
  deriving Inhabited, BEq, Repr

def CheckKind.all : Array CheckKind :=
  #[.realizable, .inst, .expect, .cover, .vacuity, .redundancy, .determinism, .definedness]

inductive Verdict where
  | pass
  | fail
  | inconclusive
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Variables' values in a model, written the way Fren writes them. -/
abbrev Assignment := Array (Name × String)

/-- Why a check failed or was inconclusive. -/
inductive Detail where
  | none
  /-- The comp's assumptions contradict each other. -/
  | vacuousAssumptions (core : Array Name)
  /-- No outputs satisfy `core` on input `input`. -/
  | conflict (input : Assignment) (core : Array Name)
  /-- A behaviour satisfying the assumptions and requirements in which the
  expectation is false. -/
  | counterexample (vals : Assignment)
  /-- A behaviour satisfying the assumptions and requirements in which the
  cover goal holds. -/
  | witness (vals : Assignment)
  /-- The trigger, or the cover goal, is ruled out by `core`. -/
  | vacuous (core : Array Name)
  /-- The constraint follows from `core`. -/
  | redundant (core : Array Name)
  /-- On input `input`, the output can be `v₁` or `v₂`. -/
  | nondeterministic (input : Assignment) (v₁ v₂ : String)
  | unknown (reason : String)
  deriving Inhabited

structure CheckResult where
  kind : CheckKind
  comp : Name
  /-- The constraint checked, the instance, or the `det out`; `none` for
  checks of a whole comp. -/
  prop? : Option Name
  /-- For `inst`: the instantiated comp, and its assumption checked. -/
  target? : Option (Name × Name) := none
  /-- For `definedness`: which index of the constraint, in order. -/
  index? : Option Nat := none
  verdict : Verdict
  detail : Detail := .none
  deriving Inhabited

inductive Outcome (V : Type) where
  /-- The goal does not follow; values of (some of) the variables. -/
  | sat (model : Array (Name × V))
  /-- The goal follows. -/
  | unsat
  | unknown (reason : String)
  deriving Inhabited

def Outcome.isUnsat : Outcome V → Bool
  | .unsat => true
  | _ => false

/-- A solver's answer, without its model (`check::Outcome`). -/
inductive Answer where
  | sat
  | unsat
  | unknown
  deriving Inhabited, BEq, DecidableEq, Repr

def Outcome.answer : Outcome V → Answer
  | .sat _ => .sat
  | .unsat => .unsat
  | .unknown _ => .unknown

/-! ## Verdicts

The decisions of the checks, separate from asking the solver. -/

/-- `realizable` from the answers to `assume_q` and `cex_q`: the verdict,
and whether to report a conflict or contradictory assumptions
(`check::realizability`). -/
def realizableVerdict (assumeQ cexQ : Answer) : Verdict × Bool × Bool :=
  if assumeQ == .unsat then (.fail, false, true)
  else match cexQ with
    | .sat => (.fail, true, false)
    | .unsat => (if assumeQ == .unknown then .inconclusive else .pass, false, false)
    | .unknown => (.inconclusive, false, false)

/-- `expect` and `inst` from the answer to their query: the verdict, and
whether to report a counterexample (`check::expectation`,
`check::instance_assumption`). -/
def expectVerdict : Answer → Verdict × Bool
  | .unsat => (.pass, false)
  | .sat => (.fail, true)
  | .unknown => (.inconclusive, false)

/-- `vacuity` and `redundancy` from the answer to their query
(`check::non_vacuity`, `check::non_redundancy`). -/
def vacuityVerdict : Answer → Verdict
  | .sat => .pass
  | .unsat => .fail
  | .unknown => .inconclusive

/-- `cover` from the answer to its query: the verdict, and whether to report
a witness or the constraints that rule the goal out (`check::cover_goal`). -/
def coverVerdict : Answer → Verdict × Bool × Bool
  | .sat => (.pass, true, false)
  | .unsat => (.fail, false, true)
  | .unknown => (.inconclusive, false, false)

/-- Whether `redundancy` is checked for a constraint, from the answer to
whether its comparison set and itself are contradictory, and whether it
failed the vacuity check (`check::redundancy_asked`). -/
def redundancyAsked (consistentQ : Answer) (vacuous : Bool) : Bool :=
  consistentQ != .unsat && !vacuous

/-- `determinism` from the answer to its query, like `expect`
(`check::determinism`). -/
def determinismVerdict : Answer → Verdict × Bool := expectVerdict

def Outcome.reason : Outcome V → String
  | .unknown r => r
  | _ => ""

/-- What the checks need from a solver. -/
structure Backend (m : Type → Type) (F V : Type) where
  /-- Can `goal` be proved from the named hypotheses? -/
  query : Array (Name × F) → (goal : F) → (wantModel : Bool) → m (Outcome V)
  falseF : F
  notF : F → F
  conj : Array F → F
  /-- `∃ outputs, f`, over the comp's `out`s. -/
  existsOutputs : F → m F
  /-- `x = v` for variable `x`, if `v` can be used in a formula. -/
  pin : Name → V → m (Option F)
  /-- `v`, written the way Fren writes values. -/
  render : Name → V → m String
  /-- `f` with each variable `x` that is not an own `in` (instance variables
  too) replaced by `primed x`, a second copy of it. -/
  prime : F → F
  /-- `x = primed x`. -/
  samePrimed : Name → F
  /-- `f` with each defined output replaced by its definition, given in
  the order of their dependencies: each definition mentions only earlier
  ones. -/
  subst : Array (Name × F) → F → F

structure VarSig where
  name : Name
  role : Role
  /-- Shown in counterexamples. -/
  isPub : Bool
  /-- A `det out`. -/
  isDet : Bool := false
  deriving Inhabited

/-- Universally quantified: not chosen by the comp (`Role.isUniversal`). -/
def VarSig.isIn (v : VarSig) : Bool := v.role.isUniversal

/-- The name of the second copy of variable `n`, for `determinism`. Never a
Fren identifier, so it cannot clash. -/
def primed (n : Name) : Name := n.appendAfter "'"

/-- An instance, with formulas over the instantiating comp's variables. -/
structure Inst (F : Type) where
  name : Name
  comp : Name
  bindings : F
  /-- The instantiated comp's assumptions, requirements and instances. -/
  behaviour : F
  /-- The instantiated comp's assumptions, each an obligation. -/
  assumes : Array (Name × F)

/-- Where an index is written, which gives the hypotheses of its definedness
query (`check::definedness`). -/
inductive IndexPlace where
  | assume
  /-- A requirement, expectation, cover goal or definition. -/
  | prop
  /-- A binding of the instance at this position. -/
  | binding (k : Nat)
  deriving Inhabited, BEq, Repr

/-- An index `q[i]` of a constraint, with the formula that it is in range
where it is evaluated: its guard implies its bounds. -/
structure IndexSite (F : Type) where
  /-- The constraint, the defined output, or the instance whose binding it is in. -/
  prop : Name
  /-- Which index of it, in order. -/
  k : Nat
  place : IndexPlace
  goal : F
  deriving Inhabited

/-- A comp, with its items as backend formulas over its variables. -/
structure Comp (F : Type) where
  path : Name
  vars : Array VarSig
  assumes : Array (Name × F)
  reqs : Array (Name × F)
  expects : Array (Name × F)
  covers : Array (Name × F) := #[]
  insts : Array (Inst F) := #[]
  /-- The triggers of the `req`s and `expect`s that have one. -/
  triggers : Array (Name × F)
  /-- Each defined output, with the equation `d = e` and its definition
  `e`, each mentioning only earlier ones (`check::definitions`). -/
  defs : Array (Name × F × F) := #[]
  indexes : Array (IndexSite F) := #[]

variable {m : Type → Type} [Monad m] {F V : Type} (b : Backend m F V)

/-- A subset of `cands` that, with `base`, still entails `goal`: minimal if
the solver decides every query (deletion-based, so the result depends only
on which queries are `unsat`).
Assumes `base ++ cands` entails it. -/
def minimize (base cands : Array (Name × F)) (goal : F) : m (Array Name) := do
  let mut keep := cands
  for (n, _) in cands do
    let trial := keep.filter (·.1 != n)
    if (← b.query (base ++ trial) goal false).isUnsat then
      keep := trial
  return keep.map (·.1)

def renderModel (vars : Array VarSig) (model : Array (Name × V)) (keep : VarSig → Bool) :
    m Assignment :=
  vars.filterMapM fun v => do
    if !keep v then return none
    let some (_, val) := model.find? (·.1 == v.name) | return none
    return some (v.name, ← b.render v.name val)

/-- The variables of `model` that are universally quantified, and not also
`out`s, for a realizability conflict. -/
def conflictInput (vars : Array VarSig) (model : Array (Name × V)) : Array (Name × V) :=
  model.filter fun (n, _) =>
    vars.any (fun v => v.name == n && v.isIn) && !vars.any fun v => v.name == n && v.role == .output

/-- `x = v` for each `x` and value `v` of `input` that can be pinned. -/
def pins (input : Array (Name × V)) : m (Array (Name × F)) :=
  input.filterMapM fun (n, v) => do
    return (← b.pin n v).map (n.appendAfter "_value", ·)

/-- The value of `n` in `model`, rendered as a value of `x`. -/
def modelValue (x : Name) (model : Array (Name × V)) (n : Name) : m String := do
  let some (_, val) := model.find? (·.1 == n) | return "?"
  b.render x val

/-- Whether a check replaces defined outputs by their definitions, rather
than assuming the equations `D` (`check::definitions`): only
realizability, whose `∃` must not range over them. -/
def CheckKind.substitutes (k : CheckKind) : Bool := k == .realizable

/-- The definitions, as equations, for the hypotheses of a check of kind `k`. -/
def Comp.defEqs (c : Comp F) (k : CheckKind) : Array (Name × F) :=
  if k.substitutes then #[] else c.defs.map fun (n, eq, _) => (n, eq)

/-- `f`, with the defined outputs replaced by their definitions for a check
of kind `k`. -/
def Comp.subst (c : Comp F) (b : Backend m F V) (k : CheckKind) (f : F) : F :=
  if k.substitutes && !c.defs.isEmpty then b.subst (c.defs.map fun (n, _, e) => (n, e)) f else f

/-- `hs`, each with the defined outputs replaced by their definitions, for
realizability. -/
def Comp.substHyps (c : Comp F) (b : Backend m F V) (hs : Array (Name × F)) : Array (Name × F) :=
  hs.map fun (n, f) => (n, c.subst b .realizable f)

/-- The assumptions, then what each instance contributes (`I`). -/
def Comp.hyps (c : Comp F) (b : Backend m F V) (upTo : Nat := c.insts.size) : Array (Name × F) :=
  c.assumes ++ (c.insts.extract 0 upTo).map fun i => (i.name, b.conj #[i.bindings, i.behaviour])

/-- `realizable`: every input allowed by the assumptions has outputs
satisfying the requirements, whatever the instances do
(`check::realizability`). Defined outputs are replaced by their
definitions, so that they are never under `∃` (`check::definitions`). -/
def checkRealizable (c : Comp F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .realizable, comp := c.path, prop? := none, verdict, detail }
  let sub := c.substHyps b
  let assumes := sub c.assumes
  let assumeQ ← b.query assumes b.falseF false
  -- `cex_q` is asked only if `assume_q` is not `unsat` (`check::realizability_protocol`).
  let cexQ ← if assumeQ.isUnsat then pure (.unknown "not asked")
    else b.query (sub (c.hyps b)) (← b.existsOutputs (c.subst b .realizable (b.conj (c.reqs.map (·.2))))) true
  let (verdict, reportsCex, reportsVacuous) := realizableVerdict assumeQ.answer cexQ.answer
  if reportsVacuous then
    return result verdict (.vacuousAssumptions (← minimize b #[] assumes b.falseF))
  if reportsCex then
    let .sat model := cexQ | return result verdict
    let input := conflictInput c.vars model
    let core ← minimize b (← pins b input) (sub c.reqs) b.falseF
    return result verdict (.conflict (← renderModel b c.vars input fun v => v.isIn && v.isPub) core)
  if verdict == .inconclusive then
    return result verdict (.unknown (if cexQ.reason.isEmpty then assumeQ.reason else cexQ.reason))
  return result verdict

/-- `inst`: an assumption of instance `k`'s comp follows from the
assumptions, `k`'s bindings and the earlier instances
(`check::instance_assumption`). -/
def checkInst (c : Comp F) (k : Nat) (i : Inst F) (a : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .inst, comp := c.path, prop? := some i.name, target? := some (i.comp, a.1), verdict, detail }
  let q ← b.query (c.defEqs .inst ++ (c.hyps b k).push (i.name, i.bindings)) a.2 true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    -- Inputs and earlier instances; later ones (and `i`) are unconstrained.
    let later := (c.insts.extract k).map (·.name)
    let shown v := v.isIn && v.isPub && !later.contains v.name.getRoot
    return result verdict (.counterexample (← renderModel b c.vars model shown))
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- `expect`: the expectation follows from the assumptions, instances and
requirements (`check::expectation`). -/
def checkExpect (c : Comp F) (e : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .expect, comp := c.path, prop? := some e.1, verdict, detail }
  let q ← b.query (c.defEqs .expect ++ (c.hyps b ++ c.reqs)) e.2 true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    return result verdict (.counterexample (← renderModel b c.vars model (·.isPub)))
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- `cover`: some behaviour satisfying the assumptions, instances and
requirements satisfies the cover goal, which a model of the negated goal
witnesses (`check::cover_goal`). -/
def checkCover (c : Comp F) (g : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .cover, comp := c.path, prop? := some g.1, verdict, detail }
  let hyps := c.hyps b ++ c.reqs
  let goal := b.notF g.2
  let q ← b.query (c.defEqs .cover ++ hyps) goal true
  match coverVerdict q.answer, q with
  | (verdict, true, _), .sat model =>
    return result verdict (.witness (← renderModel b c.vars model (·.isPub)))
  -- The core is sought only on `unsat` (`Reqs/Check#cover-goals`).
  | (verdict, _, true), _ => return result verdict (.vacuous (← minimize b (c.defEqs .cover) hyps goal))
  | (.inconclusive, _, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _, _), _ => return result verdict

/-- The hypotheses of an index's place, for `definedness`. -/
def Comp.siteHyps (c : Comp F) (b : Backend m F V) (site : IndexSite F) : Array (Name × F) :=
  match site.place with
  | .assume => c.assumes.filter (·.1 != site.prop)
  | .binding k => c.hyps b k
  | .prop => c.hyps b ++ c.reqs

/-- `definedness`: the index is in range wherever it is evaluated, given the
hypotheses of its place (`check::definedness`): for an assumption, the
other assumptions; for a binding, the assumptions and earlier instances;
otherwise the assumptions, instances and requirements. -/
def checkDefinedness (c : Comp F) (site : IndexSite F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .definedness, comp := c.path, prop? := some site.prop, index? := some site.k, verdict, detail }
  let q ← b.query (c.defEqs .definedness ++ c.siteHyps b site) site.goal true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    return result verdict (.counterexample (← renderModel b c.vars model (·.isPub)))
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- `vacuity`: the trigger can hold in some behaviour satisfying the
assumptions and requirements (`check::non_vacuity`). -/
def checkVacuity (c : Comp F) (t : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .vacuity, comp := c.path, prop? := some t.1, verdict, detail }
  let hyps := c.hyps b ++ c.reqs
  let goal := b.notF t.2
  let q ← b.query (c.defEqs .vacuity ++ hyps) goal false
  match vacuityVerdict q.answer with
  | .fail => return result .fail (.vacuous (← minimize b (c.defEqs .vacuity) hyps goal))
  | .inconclusive => return result .inconclusive (.unknown q.reason)
  | .pass => return result .pass

/-- `redundancy`: the assumption or requirement `p` does not follow from
`others`: for an assumption, the other assumptions; for a requirement, the
assumptions, instances and other requirements (`check::non_redundancy`). -/
def checkRedundant (c : Comp F) (others : Array (Name × F)) (p : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .redundancy, comp := c.path, prop? := some p.1, verdict, detail }
  let q ← b.query (c.defEqs .redundancy ++ others) p.2 false
  match vacuityVerdict q.answer with
  | .fail => return result .fail (.redundant (← minimize b (c.defEqs .redundancy) others p.2))
  | .inconclusive => return result .inconclusive (.unknown q.reason)
  | .pass => return result .pass

/-- `determinism`: any two behaviours satisfying the assumptions, instances
and requirements on the same input agree on the `det out` `x`
(`check::determinism`). -/
def checkDeterminism (c : Comp F) (x : Name) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .determinism, comp := c.path, prop? := some x, verdict, detail }
  let once := c.defEqs .determinism ++ (c.hyps b ++ c.reqs)
  let twice := once ++ once.map fun (n, f) => (primed n, b.prime f)
  let q ← b.query twice (b.samePrimed x) true
  match determinismVerdict q.answer, q with
  | (verdict, true), .sat model =>
    let input ← renderModel b c.vars model fun v => v.isIn && v.isPub && v.name.isAtomic
    return result verdict
      (.nondeterministic input (← modelValue b x model x) (← modelValue b x model (primed x)))
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- The checks of a global expectation (`Reqs/Lang/Global`), as a `Comp`
whose path is the expectation's module, with one instance per binder (no
bindings, and no assumptions as obligations) and the expectation itself. -/
def globalKinds : Array CheckKind := #[.expect, .vacuity, .definedness]

/-- The checks run on a global expectation if `global`, else on a component
(`check::applies`). -/
def kindsFor (global : Bool) : Array CheckKind :=
  if global then globalKinds else CheckKind.all

/-- The SMT-LIB logic of a check's queries (`cli::logic`): only
realizability quantifies, over outputs; a spec that uses strings or sets
(`extended`) needs `ALL`, and one that projects a relation over a type that
is not finite (`projection`), `HO_ALL`. -/
def logic (kind : CheckKind) (extended : Bool := false) (projection : Bool := false) : String :=
  if extended then (if projection then "HO_ALL" else "ALL") else match kind with
    | .realizable => "UFDTLIA"
    | _ => "QF_UFDTLIA"

/-- The cvc5 options for a spec that uses strings and sets (`cli::logic`):
`strings-exp` for the extended string functions, `re-inter-mode` to
decide intersections of patterns, `re-elim` to rewrite a match that needs
no automaton, such as `x[0-9]{2}.*`, as string functions, and `sets-exp`
to count the members of a set of a finite type. -/
def solverOptions (strings sets : Bool) : List (String × String) :=
  (if strings then [("strings-exp", "true"), ("re-inter-mode", "all"), ("re-elim", "on")] else [])
    ++ (if sets then [("sets-exp", "true")] else [])

/-- `inst` for each assumption of each instance, in order. -/
def checkInsts (c : Comp F) : m (Array CheckResult) := do
  return (← c.insts.zipIdx.mapM fun (i, k) => i.assumes.mapM (checkInst b c k i)).flatten

/-- Whether `hs` are consistent: `sat` if there are none. -/
def consistent (hs : Array (Name × F)) : m Answer := do
  if hs.isEmpty then return .sat
  return (← b.query hs b.falseF false).answer

/-- The constraints whose `vacuity` check failed. -/
def vacuousOf (vacuities : Array CheckResult) : Array Name :=
  vacuities.filterMap fun r => if r.verdict == .fail then r.prop? else none

/-- `redundancy` for each assumption, then for each requirement that is not
`vacuous`, unless they are contradictory: contradictory constraints entail
everything, and a vacuous requirement is already reported
(`check::redundancy_asked`). -/
def checkRedundancies (c : Comp F) (vacuous : Array Name) : m (Array CheckResult) := do
  let assumeQ ← consistent b (c.defEqs .redundancy ++ c.assumes)
  let assumes ← c.assumes.filterMapM fun a => do
    if redundancyAsked assumeQ false then
      return some (← checkRedundant b c (c.assumes.filter (·.1 != a.1)) a)
    return none
  let allQ ← if c.reqs.isEmpty then pure .sat else consistent b (c.defEqs .redundancy ++ (c.hyps b ++ c.reqs))
  let reqs ← c.reqs.filterMapM fun r => do
    if redundancyAsked allQ (vacuous.contains r.1) then
      return some (← checkRedundant b c (c.hyps b ++ c.reqs.filter (·.1 != r.1)) r)
    return none
  return assumes ++ reqs

/-- `determinism` for each `det out`. -/
def checkDets (c : Comp F) : m (Array CheckResult) :=
  c.vars.filterMapM fun v => do
    if v.isDet then return some (← checkDeterminism b c v.name)
    return none

/-- The results of `x` if `selected`, else none. -/
def ifSelected (selected : Bool) (x : m (Array α)) : m (Array α) := if selected then x else pure #[]

/-- All selected checks for one comp, in reporting order, each with the
backend `bk` gives for its kind. -/
def checkComp (bk : CheckKind → Backend m F V) (c : Comp F) (kinds : Array CheckKind := CheckKind.all) :
    m (Array CheckResult) := do
  let realizable ← ifSelected (kinds.contains .realizable) ((#[·]) <$> checkRealizable (bk .realizable) c)
  let insts ← ifSelected (kinds.contains .inst) (checkInsts (bk .inst) c)
  let expects ← ifSelected (kinds.contains .expect) (c.expects.mapM (checkExpect (bk .expect) c))
  let covers ← ifSelected (kinds.contains .cover) (c.covers.mapM (checkCover (bk .cover) c))
  let vacuities ← ifSelected (kinds.contains .vacuity) (c.triggers.mapM (checkVacuity (bk .vacuity) c))
  let redundancies ←
    ifSelected (kinds.contains .redundancy) (checkRedundancies (bk .redundancy) c (vacuousOf vacuities))
  let dets ← ifSelected (kinds.contains .determinism) (checkDets (bk .determinism) c)
  let defined ← ifSelected (kinds.contains .definedness) (c.indexes.mapM (checkDefinedness (bk .definedness) c))
  return realizable ++ insts ++ expects ++ covers ++ vacuities ++ redundancies ++ dets ++ defined

/-! ## Reporting

Message text shared by both front ends (`view`). -/

/-- The severity of a check's result (`view::severity`): passes are silent,
and a redundant constraint is only a warning. -/
def severity? : CheckKind → Verdict → Option Severity
  | _, .pass => none
  | .redundancy, .fail => some .warning
  | _, .fail => some .error
  | _, .inconclusive => some .warning

def CheckResult.severity? (r : CheckResult) : Option Severity := Fren.Core.severity? r.kind r.verdict

/-- The most severe of the severities of a run's results, `none` if there
are none, for the exit code (`cli::worst_severity`). -/
def worst (sevs : Array Severity) : Option Severity :=
  if sevs.any (· == .error) then some .error
  else if sevs.any (· == .warning) then some .warning
  else none

structure Message where
  severity : Severity
  /-- The comp item the message is about, or `none` for the comp itself. -/
  item? : Option Name
  /-- Point at the item's `when`/`unless` condition rather than its name. -/
  atTrigger : Bool := false
  /-- Point at the item's index with this number, in order, rather than its name. -/
  atIndex? : Option Nat := none
  msg : Msg
  deriving Inhabited

def Message.text (m : Message) : String := m.msg.text

def showNames (ns : Array Name) : String :=
  ", ".intercalate (ns.toList.map fun n => s!"`{n}`")

def showAssignment (a : Assignment) : String :=
  if a.isEmpty then "(any values)" else ", ".intercalate (a.toList.map fun (n, v) => s!"{n} = {v}")

def showComp (path : Name) : String :=
  "::".intercalate (path.components.map (·.toString))

inductive Advice where
  | raiseTimeout
  | namesConstructs
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What an inconclusive result advises (`view::inconclusive_advice`):
in the decidable core, the solver ran out of time. -/
def inconclusiveAdvice (decidable : Bool) : Advice :=
  if decidable then .raiseTimeout else .namesConstructs

/-- The messages for one result. Passing checks produce none. `decidable`
says whether the component is in the decidable core: whether no construct
of it opted out. -/
def messages (hasPrivateOuts : Bool) (r : CheckResult) (decidable : Bool := true) : Array Message :=
  -- A global expectation's `comp` is its module, which may be the root.
  let subject := s!"`{showComp (r.comp ++ (r.prop?.getD .anonymous))}`"
  -- Passes have no severity, and no messages.
  let sev := r.severity?.getD .info
  let one (code : String) (headline : String) (label? : Option String) (notes : Array String)
      (atTrigger := false) (item? := r.prop?) : Message :=
    { severity := sev, item?, atTrigger, atIndex? := r.index?, msg := { code? := some code, headline, label?, notes } }
  let priv := if hasPrivateOuts then #["note: private `out`s are not shown"] else #[]
  match r.verdict, r.detail with
  -- A cover goal's witness is information; the pass itself is silent (`Reqs/View#check-results`).
  -- A model that the backend could not read gives no values to show.
  | .pass, .witness vals =>
    #[{ severity := .info, item? := r.prop?
        msg := { code? := none, headline := s!"cover goal {subject} is met", label? := some "met"
                 notes := if vals.isEmpty then #[] else #[s!"witness: {showAssignment vals}"] ++ priv } }]
  | .pass, _ => #[]
  | .inconclusive, d =>
    let why := match d with | .unknown w => s!": {w}" | _ => ""
    let what := match r.kind, r.target? with
      | .realizable, _ => s!"{subject} is realizable"
      | .inst, some (sub, a) => s!"the assumption `{a}` of `{showComp sub}` holds for instance {subject}"
      | .inst, none => s!"{subject} holds"
      | .expect, _ => s!"{subject} holds"
      | .cover, _ => s!"{subject} can be met"
      | .vacuity, _ => s!"{subject} is vacuous"
      | .redundancy, _ => s!"{subject} is redundant"
      | .determinism, _ => s!"{subject} is determined by the inputs"
      | .definedness, _ => s!"an index of {subject} is in range"
    let advice := match inconclusiveAdvice decidable with
      | .raiseTimeout => #["note: the solver gave up, so this check neither passed nor failed",
        "help: raise the time limit with `--timeout`, or simplify the constraints involved"]
      | .namesConstructs => #["note: the solver gave up, so this check neither passed nor failed",
        "note: the component uses constructs outside the decidable core (`undecidable` is allowed), so the solver may never decide it",
        "help: bring it back into the decidable core, or raise the time limit with `--timeout`"]
    #[one "F0608" s!"could not decide whether {what}{why}" (some "undecided") advice]
  | .fail, .vacuousAssumptions core =>
    #[one "F0602" s!"the assumptions of {subject} are unsatisfiable: {showNames core} contradict each other"
      (some "no input satisfies its assumptions") #["note: every requirement would hold vacuously",
        "help: weaken or remove one of them"] (item? := none)]
  | .fail, .conflict input core =>
    -- Instance variables (`w.x`) cannot be assumed about.
    let help := if input.all (·.1.isAtomic) then #["help: weaken one of them, or add an `assume` that rules this input out"]
      else #["help: weaken one of them",
        "note: instance variables are part of the system: whatever the instances do, the component must cope"]
    #[one "F0601" s!"{subject} is not realizable: for the input {showAssignment input}, no outputs satisfy {showNames core}"
      (some "not realizable") help (item? := none)]
    ++ core.map fun n =>
      let others := core.filter (· != n)
      { severity := .info, item? := some n,
        msg := { code? := none, headline := if others.isEmpty then s!"is false when {showAssignment input}"
          else s!"conflicts with {showNames others} when {showAssignment input}" } }
  | .fail, .counterexample vals =>
    if r.kind == .definedness then
      #[one "F0611" s!"an index of {subject} may be out of range" (some "may be out of range")
        #[s!"counterexample: {showAssignment vals}",
          "note: out of range, `q[i]` is an unknown value, so the constraint says nothing useful there",
          "help: guard it with a bound, as in `i < q.len and q[i] = x`, before it in an `and`, or in a `when`"]]
    else
    if let (.inst, some (sub, a)) := (r.kind, r.target?) then
      #[one "F0604" s!"the assumption `{a}` of `{showComp sub}` may not hold for instance {subject}"
        (some s!"may violate `{showComp sub}::{a}`")
        #[s!"counterexample: {showAssignment vals}",
          "help: bind the instance's inputs so that the assumption holds, or add an `assume` that guarantees it"]]
    else
    #[one "F0603" s!"expectation {subject} does not hold" (some "does not follow from the requirements")
      (#[s!"counterexample: {showAssignment vals}"] ++ priv ++
        #["help: strengthen the requirements so that it follows, or correct the expectation"])]
  | .fail, .vacuous core =>
    if r.kind == .cover then
      let why := if core.isEmpty then "no behaviour satisfies it" else s!"it is ruled out by {showNames core}"
      #[one "F0615" s!"cover goal {subject} cannot be met: {why}" (some "no behaviour that meets the component satisfies this")
        #["note: a cover goal is a scenario that some behaviour meeting the assumptions and requirements must allow",
          "help: weaken the constraints that rule it out, or correct the goal"]]
    else
    let others := core.filter (some · != r.prop?)
    let why := if others.isEmpty then "" else s!", given {showNames others}"
    #[one "F0605" s!"{subject} is vacuous: its condition can never hold{why}" (some "this condition is always false")
      #["note: a constraint whose condition never holds says nothing",
        "help: correct the condition, or the constraints that rule it out"] (atTrigger := true)]
  | .fail, .redundant core =>
    let why := if core.isEmpty then "it always holds" else s!"it follows from {showNames core}"
    #[one "F0606" s!"{subject} is redundant: {why}" (some "redundant")
      #["help: if it is meant as a consequence, make it an `expect`, so that it is checked"]]
  | .fail, .nondeterministic input v₁ v₂ =>
    #[one "F0607" s!"{subject} is not determined by the inputs: for the input {showAssignment input}, it can be {v₁} or {v₂}"
      (some "not determined") #["note: a `det out` must have exactly one value for each input",
        "help: add requirements that pin it down, or remove `det`"]]
  | .fail, _ => #[{ severity := sev, item? := r.prop?, msg := Msg.internal s!"{subject} failed without details" }]

/-- The help of a warning from testing: from `fren check`, testing a check
set to testing, running `fren check` would not help (`Reqs/Check#checking-by-testing`). -/
def testingHelp (byCheck : Bool) (decide : String) : String :=
  if byCheck then "help: raise `--tests`; the checks set to testing are not asked of the solver"
  else s!"help: run `fren check` to {decide}, or raise `--tests`"

/-- Testing found no outputs for an admissible input (`eval::test_verdict`). -/
def noOutputsMsg (subject : String) (input : Assignment) (byCheck : Bool := false) : Msg :=
  { code? := some "F0609", headline := s!"testing found no outputs of {subject} for the input {showAssignment input}"
    label? := some "possibly not realizable"
    notes := #["note: the search tries only some values, so outputs may still exist",
      if byCheck then testingHelp true "" else "help: run `fren check` to decide whether it is realizable"] }

/-- No test reached a component's checks (`eval::test_verdict`). -/
def untestedMsg (subject : String) (tests : Nat) (byCheck : Bool := false) : Msg :=
  { code? := some "F0610", headline := s!"testing found no admissible behaviour of {subject} in {tests} tests"
    label? := some "untested"
    notes := #["note: so none of its checks were tested",
      testingHelp byCheck "decide whether its assumptions and requirements can hold"] }

/-- Testing found admissible behaviours, but none in which a check's
trigger held (`eval::reaches`). -/
def untriggeredMsg (subject : String) (tests : Nat) (byCheck : Bool := false) : Msg :=
  { code? := some "F0612", headline := s!"testing never reached {subject} in {tests} tests: its trigger held in none of them"
    label? := some "never held"
    notes := #["note: where the trigger is false the constraint holds by its trigger alone, so those tests say nothing about it",
      testingHelp byCheck "decide it"] }

/-- Testing found admissible behaviours, but none in which a cover goal
held (`Reqs/Eval#fren-quickcheck`). -/
def unwitnessedMsg (subject : String) (tests : Nat) (byCheck : Bool := false) : Msg :=
  { code? := some "F0616", headline := s!"testing found no behaviour in which cover goal {subject} holds in {tests} tests"
    label? := some "no witness found"
    notes := #["note: the search tries only some values, so such a behaviour may still exist",
      testingHelp byCheck "decide whether it can be met"] }

/-- The severity of the summary of a run (`view::summary`): always
information, whatever the results. -/
def summarySeverity (_results : Array CheckResult) : Severity := .info

/-- Which count of the summary a result is in (`view::counted`). -/
inductive Bucket where
  | passed
  | failed
  | inconclusive
  | redundant
  deriving Inhabited, BEq, DecidableEq, Repr

def bucketOf (kind : CheckKind) (verdict : Verdict) : Bucket :=
  if kind == .redundancy && verdict == .fail then .redundant
  else match verdict with
    | .pass => .passed
    | .fail => .failed
    | .inconclusive => .inconclusive

/-- Whether a result is a redundant constraint, counted apart from other
failures, which are errors (`view::summary`). -/
def CheckResult.isRedundant (r : CheckResult) : Bool := bucketOf r.kind r.verdict == .redundant

def summary (results : Array CheckResult) (byTesting : Nat := 0) : String :=
  let count (b : Bucket) := (results.filter fun r => bucketOf r.kind r.verdict == b).size
  let tested := if byTesting == 0 then "" else s!" ({byTesting} by testing)"
  s!"fren: {count .passed} passed{tested}, {count .failed} failed, {count .inconclusive} inconclusive, \
    {count .redundant} redundant"

end Fren.Core
