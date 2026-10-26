-- keep-sorted start
import FrenCore.Diagnostic
import FrenCore.Names
import FrenCore.PatternTypes
import FrenCore.Table
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
  | completeness
  | disjointness
  /-- An application meets a precondition of the function it applies. -/
  | precondition
  /-- A defined function meets a postcondition. -/
  | postcondition
  | reachability
  deriving Inhabited, DecidableEq, Repr

def CheckKind.all : Array CheckKind :=
  #[.realizable, .inst, .expect, .cover, .vacuity, .redundancy, .determinism, .definedness, .completeness, .disjointness,
    .precondition, .postcondition, .reachability]

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

/-- At a realizability conflict, a guarantee of the minimal core and the
rest of the core force an output to different values on the conflict's
input (`check::clash_notes`). -/
structure Clash where
  /-- The guarantee, where the note is. -/
  guarantee : Name
  /-- The other guarantees of the core, in its order. -/
  rest : Array Name
  output : Name
  /-- The value that `guarantee` forces `output` to. -/
  value : String
  /-- The value that `rest` forces `output` to. -/
  restValue : String
  deriving Inhabited

structure CheckResult where
  kind : CheckKind
  comp : Name
  /-- The constraint checked, the instance, or the `det out`; `none` for
  checks of a whole comp. -/
  prop? : Option Name
  /-- For `inst`: the instantiated comp, and its assumption checked; for
  `precondition`, the applied function and its precondition; for
  `postcondition`, the function and its postcondition. -/
  target? : Option (Name × Name) := none
  /-- For `definedness`: which index of the constraint, in order. -/
  index? : Option Nat := none
  /-- For `completeness`, `disjointness` and `reachability`: which of the
  constraint's questions about its tables and `match`es, in order. -/
  site? : Option Nat := none
  /-- For `disjointness`: the rows, counted from 0. -/
  rows? : Option (Nat × Nat) := none
  /-- For `completeness`, `disjointness` and `reachability`: the question. -/
  goal? : Option TableGoal := none
  /-- For `definedness`, of a value given where a pattern type is declared,
  and for `inst`, of an input of a pattern type: that type, as written
  (`Reqs/Check#pattern-types`). -/
  patTy? : Option String := none
  verdict : Verdict
  detail : Detail := .none
  /-- For `cover`: its query depends on an interpretation, so its witness's
  values are not shown (`coverInterpreted`). -/
  interpreted : Bool := false
  /-- For `realizable`, failing with a conflict: the clashes of forced
  outputs between its core's guarantees (`clashesOf`). -/
  clashes : Array Clash := #[]
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
  /-- The instantiated comp's assumptions, each an obligation, after the
  constraints of its inputs' types (`Reqs/Check#instance-assumptions`). -/
  assumes : Array (Name × F)
  /-- Which of `assumes` are its inputs' types' constraints, each with its
  type, as written. -/
  typed : Array (Name × String) := #[]

/-- Where an index or a table is written, which gives the hypotheses of its
definedness query (`check::definedness`), and of the questions about its
rows (`check::completeness`, `check::disjointness`). -/
inductive IndexPlace where
  | assume
  /-- A requirement, expectation, cover goal or definition. -/
  | prop
  /-- A binding of the instance at this position. -/
  | binding (k : Nat)
  /-- The body or a postcondition of a function, or the value of a
  constant: the function's preconditions, and the conditions around it,
  which its goal already has. -/
  | body
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
  /-- For a value given where a pattern type is declared, rather than an
  index: that type, as written (`Reqs/Check#pattern-types`). -/
  patTy? : Option String := none
  deriving Inhabited

/-- A question about the cases of a table or a `match` (`TableGoal`), where
it is written: its site's goal is the question, under its guard. -/
structure TableSite (F : Type) where
  /-- Its place, the item it is in, and which of the item's questions
  about its tables it is, in order. -/
  site : IndexSite F
  goal : TableGoal
  deriving Inhabited

/-- The check that answers a question about a split's cases, or about an
application's arguments. -/
def TableGoal.kind : TableGoal → CheckKind
  | .completeness _ => .completeness
  | .disjointness .. => .disjointness
  | .precondition .. => .precondition
  | .reachability .. => .reachability

/-- The rows that a question is about, for `disjointness`. -/
def TableGoal.rows? : TableGoal → Option (Nat × Nat)
  | .disjointness _ i j => some (i, j)
  | _ => none

/-- The function and precondition that a question is about, for
`precondition`. -/
def TableGoal.target? : TableGoal → Option (Name × Name)
  | .precondition f p => some (f, p)
  | _ => none

/-- A comp, with its items as backend formulas over its variables. -/
structure Comp (F : Type) where
  path : Name
  vars : Array VarSig
  assumes : Array (Name × F)
  reqs : Array (Name × F)
  expects : Array (Name × F)
  covers : Array (Name × F) := #[]
  insts : Array (Inst F) := #[]
  /-- The triggers of the `ensure`s and `expect`s that have one. -/
  triggers : Array (Name × F)
  /-- Each defined output, with the equation `d = e` and its definition
  `e`, each mentioning only earlier ones (`check::definitions`). -/
  defs : Array (Name × F × F) := #[]
  indexes : Array (IndexSite F) := #[]
  /-- Some variable's type, its own or an instance's, is or contains an
  abstract type. -/
  typesInterpreted : Bool := false
  /-- The questions about the cases of its tables and `match`es, and about
  the arguments of its applications of functions with preconditions. -/
  tables : Array (TableSite F) := #[]
  /-- For the body of a defined function: its postconditions, each a claim
  over its parameters (`check::postcondition`); its preconditions are its
  `assumes`. -/
  posts : Array (Name × F) := #[]
  /-- For the body or contract of a function: the function, which the
  results of `postcondition` name. -/
  fn? : Option Name := none

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

/-- Whether `hyps` force the variable `x` to `v`, its value in a model of
them: `x = v` follows from them (`check::forcing`). A value that cannot be
pinned is not known to be forced. -/
def forces (hyps : Array (Name × F)) (x : Name) (v : V) : m Bool := do
  let some f ← b.pin x v | return false
  return (← b.query hyps f false).isUnsat

/-- The clash at the guarantee `e` of the minimal core `core`, on the input
that `pinned` pins: the first of the outputs `outs` that `{e}` and the
rest of the core force to different values (`check::clash_notes`). Each
side is asked for a model, then whether each output's value in it
follows (`forces`); only the outputs whose values in the two models
differ are asked about, since sides that force an output both force its
value in their models. None if the rest is empty, which forces nothing,
or a side has no model. -/
def clashAt (pinned core : Array (Name × F)) (outs : Array Name) (e : Name) : m (Option Clash) := do
  let one := core.filter (·.1 == e)
  let rest := core.filter (·.1 != e)
  if rest.isEmpty then return none
  let .sat m₁ ← b.query (pinned ++ one) b.falseF true | return none
  let .sat m₂ ← b.query (pinned ++ rest) b.falseF true | return none
  for o in outs do
    let some (_, v₁) := m₁.find? (·.1 == o) | continue
    let some (_, v₂) := m₂.find? (·.1 == o) | continue
    let s₁ ← b.render o v₁
    let s₂ ← b.render o v₂
    if s₁ == s₂ then continue
    if !(← forces b (pinned ++ one) o v₁) then continue
    if !(← forces b (pinned ++ rest) o v₂) then continue
    return some { guarantee := e, rest := rest.map (·.1), output := o, value := s₁, restValue := s₂ }
  return none

/-- Whether `found` notes leave room for another under the budget
`examples`, `none` for no limit (`check::clash_notes`). -/
def withinBudget (found : Nat) : Option Nat → Bool
  | none => true
  | some n => found < n

/-- The clashes of a conflict, one at most at each guarantee of the
minimal core `core`, in its order, and at most `examples` in all
(`check::clash_notes`): no query is asked once they are found. -/
def clashesOf (pinned core : Array (Name × F)) (outs : Array Name) (examples : Option Nat) : m (Array Clash) := do
  let mut found := #[]
  for (e, _) in core do
    if !withinBudget found.size examples then break
    if let some cl ← clashAt b pinned core outs e then found := found.push cl
  return found

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

/-- The outputs whose values a clash note may give: the public ones that
are not defined, since realizability replaces those by their definitions. -/
def Comp.clashOutputs (c : Comp F) : Array Name :=
  (c.vars.filter fun v => v.role == .output && v.isPub && !c.defs.any (·.1 == v.name)).map (·.name)

/-- Whether the values of a realizability conflict's clash notes would
depend on an interpretation (`check::clash_notes`), as a cover goal's
witness would (`coverInterpreted`): whether some variable's type is
abstract, or some formula of the notes' queries, a guarantee or a
definition substituted into one, uses an abstract type or an
uninterpreted function, as `interprets` says of a formula. -/
def Comp.realizableInterpreted (c : Comp F) (interprets : F → Bool) : Bool :=
  c.typesInterpreted || (c.defs.map (·.2.1) ++ c.reqs.map (·.2)).any interprets

/-- The clashes of a realizability conflict on the input that `pinned`
pins, with the minimal core `core` (`clashesOf`): none if they would depend
on an interpretation (`Comp.realizableInterpreted`), or if some variable
of the input could not be pinned (`allPinned` is false), since the
queries would then not be about the input that the error shows
(`check::clash_notes`). -/
def conflictClashes (c : Comp F) (pinned : Array (Name × F)) (allPinned : Bool) (core : Array Name)
    (examples : Option Nat) (interprets : F → Bool) : m (Array Clash) :=
  if c.realizableInterpreted interprets || !allPinned then pure #[]
  else clashesOf b pinned ((c.substHyps b c.reqs).filter (core.contains ·.1)) c.clashOutputs examples

/-- `realizable`: every input allowed by the assumptions has outputs
satisfying the requirements, whatever the instances do
(`check::realizability`). Defined outputs are replaced by their
definitions, so that they are never under `∃` (`check::definitions`). A
conflict comes with at most `examples` clashes of forced outputs
(`clashesOf`), `none` for no limit, and none if they would depend on an
interpretation, as `interprets` says of a formula. -/
def checkRealizable (c : Comp F) (examples : Option Nat := some 1) (interprets : F → Bool := fun _ => false) :
    m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .realizable, comp := c.path, prop? := none, target? := c.fn?.map (·, .anonymous), verdict, detail }
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
    let pinned ← pins b input
    let core ← minimize b pinned (sub c.reqs) b.falseF
    let clashes ← conflictClashes b c pinned (pinned.size == input.size) core examples interprets
    return { result verdict (.conflict (← renderModel b c.vars input fun v => v.isIn && v.isPub) core) with clashes }
  if verdict == .inconclusive then
    return result verdict (.unknown (if cexQ.reason.isEmpty then assumeQ.reason else cexQ.reason))
  return result verdict

/-- `inst`: an assumption of instance `k`'s comp follows from the
assumptions, `k`'s bindings and the earlier instances
(`check::instance_assumption`). -/
def checkInst (c : Comp F) (k : Nat) (i : Inst F) (a : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .inst, comp := c.path, prop? := some i.name, target? := some (i.comp, a.1), verdict, detail
      patTy? := (i.typed.find? (·.1 == a.1)).map (·.2) }
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
  | .body => c.assumes

/-- `definedness`: the index is in range wherever it is evaluated, given the
hypotheses of its place (`check::definedness`): for an assumption, the
other assumptions; for a binding, the assumptions and earlier instances;
otherwise the assumptions, instances and requirements. -/
def checkDefinedness (c : Comp F) (site : IndexSite F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .definedness, comp := c.path, prop? := some site.prop, index? := some site.k, verdict, detail
      patTy? := site.patTy? }
  let q ← b.query (c.defEqs .definedness ++ c.siteHyps b site) site.goal true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    return result verdict (.counterexample (← renderModel b c.vars model (·.isPub)))
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- The questions about the rows of `c`'s tables that the checks of kind
`k` answer. -/
def Comp.tablesOf (c : Comp F) (k : CheckKind) : Array (TableSite F) := c.tables.filter (·.goal.kind == k)

/-- Whether reachability asks under a hypothesis, from whether it is one
of definedness's at the case and whether it is the constraint, definition
or binding that the case is in (`check::reach_hypothesis`). -/
def reachUses (definedness enclosing : Bool) : Bool := definedness && !enclosing

/-- The hypotheses of the checks of kind `kind` that leave out the
constraint, definition or binding that a case is in, reachability and
disjointness (`check::reach_hypothesis`): those of its place for
`definedness`, the definitions among them, but that one. -/
def Comp.caseHyps (c : Comp F) (b : Backend m F V) (kind : CheckKind) (site : IndexSite F) : Array (Name × F) :=
  (c.defEqs kind ++ c.siteHyps b site).filter fun h => reachUses true (h.1 == site.prop)

/-- The hypotheses of a case's reachability: those of its place for
`definedness`, the definitions among them, but the constraint, definition
or binding that it is in, which may rule out the behaviours that take the
case only because the case is written in it, as in `ensure r: match k { A
if ok? => true, _ => false }`, or in the definition of `y` beside `ensure
q: y = 1` (`check::reachability`). A binding's own instance is never
among them. -/
def Comp.reachHyps (c : Comp F) (b : Backend m F V) (site : IndexSite F) : Array (Name × F) :=
  c.caseHyps b .reachability site

/-- The hypotheses of a question about the cases of a table or a `match`
but reachability: those of its place, as for `definedness`, but for
disjointness, which leaves out the constraint, definition or binding that
the table is in, as reachability does (`Comp.caseHyps`): it holds only
where the table has the value it needs, so it would hide two rows that
overlap where it does not (`check::disjointness`). -/
def Comp.tableHyps (c : Comp F) (b : Backend m F V) (t : TableSite F) : Array (Name × F) :=
  if t.goal.kind == .disjointness then c.caseHyps b .disjointness t.site
  else c.defEqs t.goal.kind ++ c.siteHyps b t.site

/-- `completeness` or `disjointness`: what the question about the cases of
a table or a `match` asks holds wherever it is evaluated, given the
hypotheses of its place (`Comp.tableHyps`) (`check::completeness`,
`check::disjointness`). -/
def checkTable (c : Comp F) (t : TableSite F) : m CheckResult := do
  let kind := t.goal.kind
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind, comp := c.path, prop? := some t.site.prop, site? := some t.site.k, rows? := t.goal.rows?,
      target? := t.goal.target?, goal? := some t.goal, verdict, detail }
  let q ← b.query (c.tableHyps b t) t.site.goal true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    return result verdict (.counterexample (← renderModel b c.vars model (·.isPub)))
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- `postcondition`: the postcondition `p` of a defined function, named
after the function and the clause, follows from its preconditions, its
parameters free (`check::postcondition`). -/
def checkPostcondition (c : Comp F) (p : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .postcondition, comp := c.path, prop? := some p.1, target? := c.fn?.map (·, Name.mkSimple p.1.getString!),
      verdict, detail }
  let q ← b.query c.assumes p.2 true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    return result verdict (.counterexample (← renderModel b c.vars model (·.isPub)))
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- `reachability`: the case of a table or a `match` that the question is
about can be taken somewhere it is evaluated, given the hypotheses of its
place but the constraint it is in (`Comp.reachHyps`): its goal, that the
case is not taken there, cannot be proved, as for `vacuity`
(`check::reachability`). -/
def checkReach (c : Comp F) (t : TableSite F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .reachability, comp := c.path, prop? := some t.site.prop, site? := some t.site.k, goal? := some t.goal
      verdict, detail }
  let q ← b.query (c.reachHyps b t.site) t.site.goal false
  match vacuityVerdict q.answer with
  | .inconclusive => return result .inconclusive (.unknown q.reason)
  | verdict => return result verdict

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
def globalKinds : Array CheckKind :=
  #[.expect, .vacuity, .definedness, .completeness, .disjointness, .precondition, .reachability]

/-- The checks of the tables, `match`es and applications in the body and contract of
a function or the value of a constant, and of a defined function's
postconditions (`check::applies`), as a `Comp` whose path is its module,
with its parameters as inputs and its preconditions as assumptions. -/
def bodyKinds : Array CheckKind := #[.definedness, .completeness, .disjointness, .precondition, .postcondition, .reachability]

/-- The checks of the contract of an uninterpreted function with
postconditions (`check::applies`), as a `Comp` whose path is its module,
with its parameters as inputs, its value as its one `out`, its
preconditions as assumptions and its postconditions, of its value, as
guarantees: whether they can hold together, and the tables and
applications in its clauses. -/
def contractKinds : Array CheckKind := #[.realizable, .completeness, .disjointness, .precondition, .reachability]

/-- The checks run on a global expectation if `global`, else on a component
(`check::applies`). -/
def kindsFor (global : Bool) : Array CheckKind :=
  if global then globalKinds else CheckKind.all

/-- What the checks run on (`check::CheckedItem`). -/
inductive CheckedItem where
  | component
  | global
  /-- The body and contract of a function, or the value of a constant. -/
  | body
  /-- The contract of an uninterpreted function with postconditions. -/
  | contract
  deriving Inhabited, DecidableEq, Repr

/-- The checks run on an item (`check::applies`). -/
def CheckedItem.kinds : CheckedItem → Array CheckKind
  | .component => kindsFor false
  | .global => kindsFor true
  | .body => bodyKinds
  | .contract => contractKinds

/-- The SMT-LIB logic of a check's queries (`cli::logic`): only
realizability quantifies, over outputs; a spec that uses strings or sets
(`extended`) needs `ALL`, and one that projects a relation over a type that
is not finite (`projection`), `HO_ALL`. -/
def logic (kind : CheckKind) (extended : Bool := false) (projection : Bool := false) : String :=
  if extended then (if projection then "HO_ALL" else "ALL") else match kind with
    | .realizable => "UFDTLIA"
    | _ => "QF_UFDTLIA"

/-- The symbols of cvc5's theories, under `HO_ALL`, that a Fren name can
spell: cvc5 rejects a declaration of any of them, quoted or not, as
shadowing a theory function symbol. Found by declaring each identifier of
cvc5's libraries as a constant. -/
def theorySymbols : Std.HashSet String := .ofList [
  "abs", "and", "arccos", "arccot", "arccsc", "arcsec", "arcsin", "arctan", "bag", "bag.all",
  "bag.card", "bag.choose", "bag.count", "bag.difference_remove", "bag.difference_subtract",
  "bag.filter", "bag.fold", "bag.inter_min", "bag.map", "bag.member", "bag.partition", "bag.setof",
  "bag.some", "bag.subbag", "bag.union_disjoint", "bag.union_max", "bv2nat", "bvadd", "bvand",
  "bvashr", "bvcomp", "bvite", "bvlshr", "bvmul", "bvnand", "bvneg", "bvnego", "bvnor", "bvnot",
  "bvor", "bvredand", "bvredor", "bvsaddo", "bvsdiv", "bvsdivo", "bvsge", "bvsgt", "bvshl",
  "bvsle", "bvslt", "bvsmod", "bvsmulo", "bvsrem", "bvssubo", "bvsub", "bvuaddo", "bvudiv",
  "bvuge", "bvugt", "bvule", "bvult", "bvumulo", "bvurem", "bvusubo", "bvxnor", "bvxor", "concat",
  "cos", "cot", "csc", "distinct", "div", "div_total", "eqrange", "exists", "exp", "ff.add",
  "ff.bitsum", "ff.mul", "ff.neg", "forall", "fp", "fp.abs", "fp.add", "fp.div", "fp.eq", "fp.fma",
  "fp.geq", "fp.gt", "fp.isInfinite", "fp.isNaN", "fp.isNegative", "fp.isNormal", "fp.isPositive",
  "fp.isSubnormal", "fp.isZero", "fp.leq", "fp.lt", "fp.max", "fp.min", "fp.mul", "fp.neg",
  "fp.rem", "fp.roundToIntegral", "fp.sqrt", "fp.sub", "fp.to_real", "int.log2", "int.pow2",
  "is_int", "ite", "lambda", "mod", "mod_total", "not", "nullable.is_null", "nullable.is_some",
  "nullable.lift", "nullable.some", "nullable.val", "or", "piand", "pto", "re.comp", "re.diff",
  "re.inter", "re.opt", "re.range", "re.union", "rel.aggr", "rel.group", "rel.iden", "rel.join",
  "rel.join_image", "rel.product", "rel.project", "rel.table_join", "rel.tclosure",
  "rel.transpose", "sbv_to_int", "sec", "select", "sep", "seq.at", "seq.contains", "seq.extract",
  "seq.indexof", "seq.len", "seq.nth", "seq.prefixof", "seq.replace", "seq.replace_all", "seq.rev",
  "seq.suffixof", "seq.unit", "seq.update", "set.all", "set.card", "set.choose", "set.complement",
  "set.comprehension", "set.filter", "set.fold", "set.insert", "set.inter", "set.is_empty",
  "set.is_singleton", "set.map", "set.member", "set.minus", "set.singleton", "set.some",
  "set.subset", "set.union", "sin", "sqrt", "store", "str.at", "str.contains", "str.from_code",
  "str.from_int", "str.in_re", "str.indexof", "str.indexof_re", "str.is_digit", "str.len",
  "str.prefixof", "str.replace", "str.replace_all", "str.replace_re", "str.replace_re_all",
  "str.rev", "str.substr", "str.suffixof", "str.to_code", "str.to_int", "str.to_lower",
  "str.to_re", "str.to_upper", "str.update", "table.aggr", "table.group", "table.join",
  "table.product", "table.project", "tan", "to_int", "to_real", "tuple", "tuple.project",
  "ubv_to_int", "wand", "xor"
]

/-- The name that the solver knows the name `s` by, in both front ends
(`Reqs/Cli#solver-queries`): `s`, or with a `#` after it if it is a
theory's symbol (`theorySymbols`), since no Fren name contains `#`. -/
def smtName (s : String) : String := if theorySymbols.contains s then s!"{s}#" else s

/-- The cvc5 options for a spec that uses strings and sets (`cli::logic`):
`strings-exp` for the extended string functions, `re-inter-mode` to
decide intersections of patterns, `re-elim` to rewrite a match that needs
no automaton, such as `x[0-9]{2}.*`, as string functions, and `sets-exp`
to count the members of a set of a finite type. -/
def solverOptions (strings sets : Bool) : List (String × String) :=
  (if strings then [("strings-exp", "true"), ("re-inter-mode", "all"), ("re-elim", "on")] else [])
    ++ (if sets then [("sets-exp", "true")] else [])

/-- The cvc5 option for a query with a quantifier over a collection's
elements, which a pattern type within an element type brings
(`Reqs/Cli#solver-queries`): `fmf-bound`, with which cvc5 finds models of
quantifiers that membership bounds. -/
def boundedOptions : List (String × String) := [("fmf-bound", "true")]

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

/-- Whether some `vacuity` query answered `sat`, its check passing: its
hypotheses are the definitions, `A`, `I` and `R`, with a trigger, so they
are satisfiable. -/
def satisfiedOf (vacuities : Array CheckResult) : Bool :=
  vacuities.any (·.verdict == .pass)

/-- `redundancy` for each assumption, then for each requirement that is not
`vacuous`, unless they are contradictory: contradictory constraints entail
everything, and a vacuous requirement is already reported
(`check::redundancy_asked`). If `satisfied`, the definitions, `A`, `I` and
`R` are known to be satisfiable (`satisfiedOf`), so neither question of
consistency is asked: its answer is `sat`. -/
def checkRedundancies (c : Comp F) (vacuous : Array Name) (satisfied : Bool := false) : m (Array CheckResult) := do
  let assumeQ ← if satisfied then pure .sat else consistent b (c.defEqs .redundancy ++ c.assumes)
  let assumes ← c.assumes.filterMapM fun a => do
    if redundancyAsked assumeQ false then
      return some (← checkRedundant b c (c.assumes.filter (·.1 != a.1)) a)
    return none
  let allQ ← if c.reqs.isEmpty || satisfied then pure .sat
    else consistent b (c.defEqs .redundancy ++ (c.hyps b ++ c.reqs))
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
backend `bk` gives for its kind. A realizability conflict has at most
`examples` clash notes, `none` for no limit, and none where `interprets`
says that their queries depend on an interpretation
(`Comp.realizableInterpreted`). -/
def checkComp (bk : CheckKind → Backend m F V) (c : Comp F) (kinds : Array CheckKind := CheckKind.all)
    (examples : Option Nat := some 1) (interprets : F → Bool := fun _ => false) : m (Array CheckResult) := do
  let realizable ← ifSelected (kinds.contains .realizable)
    ((#[·]) <$> checkRealizable (bk .realizable) c examples interprets)
  let insts ← ifSelected (kinds.contains .inst) (checkInsts (bk .inst) c)
  let expects ← ifSelected (kinds.contains .expect) (c.expects.mapM (checkExpect (bk .expect) c))
  let covers ← ifSelected (kinds.contains .cover) (c.covers.mapM (checkCover (bk .cover) c))
  let vacuities ← ifSelected (kinds.contains .vacuity) (c.triggers.mapM (checkVacuity (bk .vacuity) c))
  let redundancies ←
    ifSelected (kinds.contains .redundancy)
      (checkRedundancies (bk .redundancy) c (vacuousOf vacuities) (satisfiedOf vacuities))
  let dets ← ifSelected (kinds.contains .determinism) (checkDets (bk .determinism) c)
  let defined ← ifSelected (kinds.contains .definedness) (c.indexes.mapM (checkDefinedness (bk .definedness) c))
  let complete ← ifSelected (kinds.contains .completeness) ((c.tablesOf .completeness).mapM (checkTable (bk .completeness) c))
  let disjoint ← ifSelected (kinds.contains .disjointness) ((c.tablesOf .disjointness).mapM (checkTable (bk .disjointness) c))
  let pres ← ifSelected (kinds.contains .precondition) ((c.tablesOf .precondition).mapM (checkTable (bk .precondition) c))
  let posts ← ifSelected (kinds.contains .postcondition) (c.posts.mapM (checkPostcondition (bk .postcondition) c))
  let reach ← ifSelected (kinds.contains .reachability) ((c.tablesOf .reachability).mapM (checkReach (bk .reachability) c))
  return realizable ++ insts ++ expects ++ covers ++ vacuities ++ redundancies ++ dets ++ defined ++ complete ++ disjoint
    ++ pres ++ posts ++ reach

/-- What the applications of uninterpreted functions in a query bring
(`Reqs/Check`): for each application that `appsOf` finds in the query's
own hypotheses and goal, each once, the facts that `factsOf` gives of it:
that it is at least 0, named `nat`, if its result is a `Nat`, that it
matches its result type, named `type`, if that brings a constraint, and that it
meets each postcondition of its function where its arguments meet the
preconditions, named by the postcondition. They are in one order in both
front ends: the hypotheses' in order and then the goal's, and within a
formula in the order that `appsOf` gives, which is that of a walk of the
formula that meets an application before its arguments and the arguments
from left to right; and of each application, in the order `factsOf`
gives. Both front ends give a query these and no others, so that they
depend only on its formulas: a query never has a fact about an
application that it does not mention, as of an instantiated component's
expectation, and the formulas that `coverInterpreted` reads are all it
uses. -/
def appFacts [Monad m] [BEq F] (appsOf : F → Array F) (factsOf : F → m (Array (Name × F))) (hyps : Array (Name × F))
    (goal : F) : m (Array (Name × F)) := do
  let apps := (hyps.map (·.2) ++ #[goal]).foldl (init := #[]) fun acc f =>
    (appsOf f).foldl (init := acc) fun acc a => if acc.contains a then acc else acc.push a
  return (← apps.mapM factsOf).flatten

/-- The questions that an application of the function `f` asks of its
arguments, for the precondition check (`check::application_contract`):
each of its preconditions `pres`, at the arguments, where the
application's guard holds, as `guarded` puts it. Both front ends record
these. -/
def preconditionQuestions (guarded : F → F) (f : Name) (pres : Array (Name × F)) : Array (TableGoal × F) :=
  pres.map fun (p, g) => (.precondition f p, guarded g)

/-- The facts that an application of an uninterpreted function brings of
its postconditions `posts`, each named by its postcondition, at the
arguments and the application's value (`check::application_contract`):
each holds where its preconditions `pres` imply it, as `implies` puts it.
Both front ends' `factsOf` give these, after the application's `nat`. -/
def postconditionFacts (implies : Array F → F → F) (pres : Array F) (posts : Array (Name × F)) : Array (Name × F) :=
  posts.map fun (n, q) => (n, implies pres q)

/-- The component that checks the realizability of the contract of the
uninterpreted function `f` (`Reqs/Check#contracts-of-uninterpreted-functions`),
whose path is its module `path`: its parameters `params` as inputs, its
value `value` as its one output, and its preconditions `pres` and
postconditions `posts`, of the value, as its assumptions and guarantees,
with `sites`, the questions about the tables and applications in its
clauses. Both front ends check this component. -/
def contractComp (path f : Name) (params : Array Name) (value : Name) (pres posts : Array (Name × F))
    (sites : Array (TableSite F) := #[]) : Comp F :=
  { path, vars := params.map (fun x => { name := x, role := .input, isPub := true }) |>.push
      { name := value, role := .output, isPub := true }
    assumes := pres, reqs := posts, expects := #[], triggers := #[], tables := sites, fn? := some f }

/-- The formulas of the query of the cover goal `g` (`checkCover`): the
definitions, the assumptions, each instance's bindings and the meaning of
its component, the requirements, and the goal. No expectation or other
cover goal is among them. -/
def Comp.coverFormulas (c : Comp F) (g : F) : Array F :=
  c.defs.map (·.2.1) ++ c.assumes.map (·.2) ++ c.insts.flatMap (fun i => #[i.bindings, i.behaviour])
    ++ c.reqs.map (·.2) ++ #[g]

/-- Whether a witness of the cover goal `n` of `c` depends on an
interpretation, so that its values are not shown (`Reqs/View#check-results`):
whether some variable's type is abstract, or some formula of its query uses
an abstract type or an uninterpreted function, as `interprets` says of a
formula. Both front ends decide it so. -/
def coverInterpreted (c : Comp F) (interprets : F → Bool) (n : Name) : Bool :=
  c.typesInterpreted || match c.covers.find? (·.1 == n) with
    | some (_, g) => (c.coverFormulas g).any interprets
    | none => false

/-- `rs`, with each cover goal's result marked by `coverInterpreted`. -/
def withInterpreted (c : Comp F) (interprets : F → Bool) (rs : Array CheckResult) : Array CheckResult :=
  rs.map fun r => if r.kind == .cover then { r with interpreted := r.prop?.any (coverInterpreted c interprets) } else r

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
  /-- Point at the place of the item's question about its tables with this
  number, in order, rather than its name. -/
  atSite? : Option Nat := none
  msg : Msg
  deriving Inhabited

def Message.text (m : Message) : String := m.msg.text

def showNames (ns : Array Name) : String :=
  ", ".intercalate (ns.toList.map fun n => s!"`{n}`")

def showAssignment (a : Assignment) : String :=
  if a.isEmpty then "(any values)" else ", ".intercalate (a.toList.map fun (n, v) => s!"{n} = {v}")

/-- `` `a`, `b` and `c` ``: names in prose. -/
def showNamesAnd (ns : Array Name) : String :=
  match ns.toList.map (s!"`{·}`") |>.reverse with
  | [] => ""
  | [n] => n
  | last :: rest => s!"{", ".intercalate rest.reverse} and {last}"

/-- The note of a realizability conflict (`Reqs/View#check-results`): the
input, or the arguments of a function (`what`), one variable to a line,
and then what no outputs satisfy, `unmet`. -/
def conflictNote (what : String) (input : Assignment) (unmet : String) : String :=
  if input.isEmpty then s!"note: {unmet}"
  else s!"note: for the {what}\n" ++ String.join (input.toList.map fun (n, v) => s!"    {n} = {v}\n") ++ unmet

/-- The headline of a clash note (`view::clash_text`): the guarantee
`g` forces the output `o` to `v`, and the `count` others of its conflict,
named as the list `others`, force it to `w`. -/
def clashLine (g o v others w : String) (count : Nat) : String :=
  s!"`{g}` forces {o} = {v}, but {others}{if count = 1 then " forces " else " force "}{o} = {w}"

/-- The headline of a clash note (`Reqs/View#check-results`), at its
guarantee, with the rest of the core named `rest`. -/
def clashText (cl : Clash) (rest : Array Name) : String :=
  clashLine cl.guarantee.getString! (toString cl.output) cl.value (showNamesAnd rest) cl.restValue rest.size

/-- The note at a guarantee of a realizability conflict's core
(`Reqs/View#check-results`), one at each: its clash, if it has one
(`clashText`); else the other guarantees of the core, `others`, that it
conflicts with; or, in a core of one, that it is false for the input that
the error's note gives. `rest` names a clash's others. -/
def memberText (clash? : Option Clash) (others : Array Name) (rest : Clash → Array Name) : String :=
  match clash? with
  | some cl => clashText cl (rest cl)
  | none => if others.isEmpty then "is false for this input" else s!"conflicts with {showNamesAnd others}"

/-- The case that a question about a split is about, as a message names
it, from 1. -/
def caseText : Option TableGoal → String
  | some (.reachability .match j) => s!"arm {j + 1}"
  | some (.reachability .table j) => s!"row {j + 1}"
  | some (.reachability .tableMatch j) => s!"arm {j + 1}"
  | _ => "a case"

/-- The split that a question is about, as a message names it. -/
def splitText : Option TableGoal → String
  | some (.reachability .match _) | some (.completeness .match) => "a `match`"
  | _ => "a table"

/-- Rows `i` and `j`, counted from 0, as a message names them, from 1:
arms, of a table over a scrutinee (`arms`). -/
def rowsText (rows? : Option (Nat × Nat)) (arms : Bool := false) : String :=
  let what := if arms then "arms" else "rows"
  match rows? with
  | some (i, j) => s!"{what} {i + 1} and {j + 1}"
  | none => s!"two {what}"

/-- The name of a clause of a contract, without its function's
(`Comp.fn?`). -/
def clauseName (n : Name) : Name := Name.mkSimple n.getString!

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

/-- The messages for one result. Passing checks produce none, but for a
cover goal's witness. `decidable` says whether the component is in the
decidable core: whether no construct of it opted out. A witness whose query
depends on an interpretation (`CheckResult.interpreted`) is shown without
its values. -/
def messages (hasPrivateOuts : Bool) (r : CheckResult) (decidable : Bool := true) : Array Message :=
  -- A global expectation's `comp` is its module, which may be the root.
  let subject := s!"`{showComp (r.comp ++ (r.prop?.getD .anonymous))}`"
  -- Passes have no severity, and no messages.
  let sev := r.severity?.getD .info
  let one (code : String) (headline : String) (label? : Option String) (notes : Array String)
      (atTrigger := false) (item? := r.prop?) : Message :=
    { severity := sev, item?, atTrigger, atIndex? := r.index?, atSite? := r.site?
      msg := { code? := some code, headline, label?, notes } }
  let priv := if hasPrivateOuts then #["note: private `out`s are not shown"] else #[]
  match r.verdict, r.detail with
  -- A cover goal's witness is information; the pass itself is silent
  -- (`Reqs/View#check-results`). Its values are shown only where they mean
  -- the same to both front ends: without an interpretation.
  | .pass, .witness vals =>
    #[{ severity := .info, item? := r.prop?
        msg := { code? := none, headline := s!"cover goal {subject} is met", label? := some "met"
                 notes := if r.interpreted then #["note: the witness is not shown, since its query uses abstract types or functions, whose interpretation it depends on"]
                   else #[s!"witness: {showAssignment vals}"] ++ priv } }]
  | .pass, _ => #[]
  | .inconclusive, d =>
    let why := match d with | .unknown w => s!": {w}" | _ => ""
    let what := match r.kind, r.target? with
      | .realizable, some (f, _) => s!"the postconditions of `{showComp f}` can hold"
      | .realizable, _ => s!"{subject} is realizable"
      | .inst, some (sub, a) => match r.patTy? with
        | some ty => s!"the input `{a.getPrefix}` of `{showComp sub}` has its type `{ty}` for instance {subject}"
        | none => s!"the assumption `{a}` of `{showComp sub}` holds for instance {subject}"
      | .inst, none => s!"{subject} holds"
      | .expect, _ => s!"{subject} holds"
      | .cover, _ => s!"{subject} can be met"
      | .vacuity, _ => s!"{subject} is vacuous"
      | .redundancy, _ => s!"{subject} is redundant"
      | .determinism, _ => s!"{subject} is determined by the inputs"
      | .definedness, _ => match r.patTy? with
        | some ty => s!"a value in {subject} has the type `{ty}`"
        | none => s!"an index of {subject} is in range"
      | .completeness, _ => match r.goal? with
        | some (.completeness .match) => s!"some arm of a `match` in {subject} is taken"
        | some (.completeness .tableMatch) => s!"some arm of a table in {subject} is taken"
        | _ => s!"some row of a table in {subject} holds"
      | .disjointness, _ =>
        s!"{rowsText r.rows? (r.goal? matches some (.disjointness .tableMatch ..))} of a table in {subject} are disjoint"
      | .precondition, some (f, p) => s!"the precondition `{p}` of `{showComp f}` holds at an application in {subject}"
      | .precondition, none => s!"a precondition holds at an application in {subject}"
      | .postcondition, some (f, p) => s!"the postcondition `{p}` of `{showComp f}` holds"
      | .postcondition, none => s!"{subject} holds"
      | .reachability, _ => s!"{caseText r.goal?} of {splitText r.goal?} in {subject} can be taken"
    let advice := match inconclusiveAdvice decidable with
      | .raiseTimeout => #["note: the solver gave up, so this check neither passed nor failed",
        "help: raise the time limit with `--timeout`, or simplify the constraints involved"]
      | .namesConstructs => #["note: the solver gave up, so this check neither passed nor failed",
        "note: the component uses constructs outside the decidable core (`undecidable` is allowed), so the solver may never decide it",
        "help: bring it back into the decidable core, or raise the time limit with `--timeout`"]
    #[one "F0608" s!"could not decide whether {what}{why}" (some "undecided") advice]
  | .fail, .vacuousAssumptions core =>
    if let some (f, _) := r.target? then
      #[one "F0632" s!"the preconditions of `{showComp f}` are unsatisfiable: {showNames (core.map clauseName)} contradict each other"
        (some "no arguments meet its preconditions") #["note: the function could never be applied where its contract says anything",
          "help: weaken or remove one of them"] (item? := none)]
    else
    #[one "F0602" s!"the assumptions of {subject} are unsatisfiable: {showNames core} contradict each other"
      (some "no input satisfies its assumptions") #["note: every guarantee would hold vacuously",
        "help: weaken or remove one of them"] (item? := none)]
  | .fail, .conflict input core =>
    let contract := r.target?.map (·.1)
    let names := if contract.isSome then core.map clauseName else core
    let clashNotes := core.map fun n =>
      let short (ns : Array Name) := if contract.isSome then ns.map clauseName else ns
      let headline := memberText (r.clashes.find? (·.guarantee == n)) (short (core.filter (· != n))) fun cl => short cl.rest
      { severity := .info, item? := some n, msg := { code? := none, headline } }
    if let some f := contract then
      #[one "F0631" s!"the postconditions of `{showComp f}` cannot all hold" (some "unrealizable contract")
        #[conflictNote "arguments" input s!"no value of `{showComp f}` satisfies {showNamesAnd names}",
          "note: an uninterpreted function's postconditions are assumed wherever it is applied, so if they cannot hold, every check that applies it would pass",
          "help: weaken one of them, or add a precondition that rules these arguments out"] (item? := none)]
      ++ clashNotes
    else
    -- Instance variables (`w.x`) cannot be assumed about.
    let help := if input.all (·.1.isAtomic) then #["help: weaken one of them, or add an `assume` that rules this input out"]
      else #["help: weaken one of them",
        "note: instance variables are part of the system: whatever the instances do, the component must cope"]
    #[one "F0601" s!"{subject} is not realizable" (some "not realizable")
      (#[conflictNote "input" input s!"no outputs satisfy {showNamesAnd names}"] ++ help) (item? := none)]
    ++ clashNotes
  | .fail, .counterexample vals =>
    if let (.definedness, some ty) := (r.kind, r.patTy?) then
      let m := obligationMsg subject ty (showAssignment vals) priv
      #[one "F0622" m.headline m.label? m.notes]
    else
    if let (.inst, some (sub, a), some ty) := (r.kind, r.target?, r.patTy?) then
      let m := instanceTypeMsg subject (showComp sub) (a.getPrefix.toString) ty (showAssignment vals)
      #[one "F0623" m.headline m.label? m.notes]
    else
    if r.kind == .definedness then
      #[one "F0611" s!"an index of {subject} may be out of range" (some "may be out of range")
        #[s!"counterexample: {showAssignment vals}",
          "note: out of range, `q[i]` is an unknown value, so the constraint says nothing useful there",
          "help: guard it with a bound, as in `i < q.len and q[i] = x`, before it in an `and`, or in a `when`"]]
    else
    if r.kind == .completeness && r.goal? == some (.completeness .match) then
      #[one "F0625" s!"a `match` in {subject} may have no arm that is taken" (some "may have no arm that is taken")
        #[s!"counterexample: {showAssignment vals}",
          "note: where no arm is taken, the `match` is an unknown value, so the constraint says nothing useful there",
          "help: add an arm for this case, or end the `match` with `_ => e`"]]
    else
    if r.kind == .completeness && r.goal? == some (.completeness .tableMatch) then
      #[one "F0637" s!"a table in {subject} may have no arm that is taken" (some "may have no arm that is taken")
        #[s!"counterexample: {showAssignment vals}",
          "note: where no arm is taken, the table is an unknown value, so the constraint says nothing useful there",
          "help: add an arm for this case, or end the table with `_ => e`"]]
    else
    if r.kind == .completeness then
      #[one "F0618" s!"a table in {subject} may have no row that holds" (some "may have no row that holds")
        #[s!"counterexample: {showAssignment vals}",
          "note: where no row holds, the table is an unknown value, so the constraint says nothing useful there",
          "help: add a row for this case, or end the table with `_ => e`"]]
    else
    if r.kind == .disjointness && r.goal? matches some (.disjointness .tableMatch ..) then
      #[one "F0636" s!"{rowsText r.rows? true} of a table in {subject} may both be taken" (some "overlaps an earlier arm")
        #[s!"witness: {showAssignment vals}",
          "note: the arms of a table are disjoint, so that its value does not depend on their order, but here both patterns match and both guards hold",
          "help: make the guards exclusive, as in `V(x) if x > 0 => a, V(x) if x <= 0 => b`"]]
    else
    if r.kind == .disjointness then
      #[one "F0619" s!"{rowsText r.rows?} of a table in {subject} may both hold" (some "overlaps an earlier row")
        #[s!"witness: {showAssignment vals}",
          "note: where rows overlap, the first of them gives the table's value, so the order of the rows matters",
          "help: make the conditions exclusive, as in `a => x, not a and b => y`"]]
    else
    if let (.precondition, some (f, p)) := (r.kind, r.target?) then
      #[one "F0629" s!"the precondition `{p}` of `{showComp f}` may not hold at this application in {subject}"
        (some s!"may violate `{showComp f}::{p}`")
        #[s!"counterexample: {showAssignment vals}",
          "note: where a precondition fails, the application's value is unknown, or not what the function is for",
          "help: guard the application, as in `p(x) and f(x) = y`, or assume what the precondition needs"]]
    else
    if let (.postcondition, some (f, p)) := (r.kind, r.target?) then
      #[one "F0630" s!"the postcondition `{p}` of `{showComp f}` does not hold" (some "does not follow from the body")
        #[s!"counterexample: {showAssignment vals}",
          "help: correct the body or the postcondition, or add a precondition that rules this case out"]]
    else
    if let (.inst, some (sub, a)) := (r.kind, r.target?) then
      #[one "F0604" s!"the assumption `{a}` of `{showComp sub}` may not hold for instance {subject}"
        (some s!"may violate `{showComp sub}::{a}`")
        #[s!"counterexample: {showAssignment vals}",
          "help: bind the instance's inputs so that the assumption holds, or add an `assume` that guarantees it"]]
    else
    #[one "F0603" s!"expectation {subject} does not hold" (some "does not follow from the guarantees")
      (#[s!"counterexample: {showAssignment vals}"] ++ priv ++
        #["help: strengthen the guarantees so that it follows, or correct the expectation"])]
  | .fail, .vacuous core =>
    if r.kind == .cover then
      let why := if core.isEmpty then "no behaviour satisfies it" else s!"it is ruled out by {showNames core}"
      #[one "F0615" s!"cover goal {subject} cannot be met: {why}" (some "no behaviour that meets the component satisfies this")
        #["note: a cover goal is a scenario that some behaviour meeting the assumptions and guarantees must allow",
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
        "help: add guarantees that pin it down, or remove `det`"]]
  | .fail, _ =>
    match r.kind, r.goal? with
    | .reachability, some (.reachability .match j) =>
      #[one "F0626" s!"arm {j + 1} of a `match` in {subject} is never taken" (some "never taken")
        #["note: wherever the `match` is evaluated, its pattern or guard fails, or an earlier arm is taken",
          "help: correct its guard or the arms before it, or remove it"]]
    | .reachability, some (.reachability .table j) =>
      #[one "F0627" s!"row {j + 1} of a table in {subject} is never the first that holds" (some "never the first that holds")
        #["note: wherever the table is evaluated, an earlier row holds, or this row's condition fails",
          "help: correct its condition or the rows before it, or remove it"]]
    | .reachability, some (.reachability .tableMatch j) =>
      #[one "F0638" s!"arm {j + 1} of a table in {subject} is never taken" (some "never taken")
        #["note: wherever the table is evaluated, its pattern or guard fails, or another arm is taken",
          "help: correct its guard or the arms that take its cases, or remove it"]]
    | _, _ => #[{ severity := sev, item? := r.prop?, msg := Msg.internal s!"{subject} failed without details" }]

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
      testingHelp byCheck "decide whether its assumptions and guarantees can hold"] }

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

/-- What both front ends say instead of checking, after a static error
(`Reqs/View#static-errors`). It does not count them: the `fren` command
stops at a parse error, where Lean goes on and may find more. -/
def couldNotHeadline (what := "check") : String :=
  s!"could not {what} due to previous errors"

def summary (results : Array CheckResult) (byTesting : Nat := 0) : String :=
  let count (b : Bucket) := (results.filter fun r => bucketOf r.kind r.verdict == b).size
  let tested := if byTesting == 0 then "" else s!" ({byTesting} by testing)"
  s!"fren: {count .passed} passed{tested}, {count .failed} failed, {count .inconclusive} inconclusive, \
    {count .redundant} redundant"

end Fren.Core
