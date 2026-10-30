-- keep-sorted start
import FrenCore.Diagnostic
import FrenCore.Names
import FrenCore.PatternTypes
import FrenCore.Recursion
import FrenCore.SeqElems
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

/-- What Fren's semantics, at the values read from a solver's model, says
against the solver's answer (`model::contradicted?`): a hypothesis of the
query is false there, or its goal is true. -/
inductive Contradiction where
  | hypothesis (name : Name)
  | goal
  deriving Inhabited, BEq, Repr

/-- What the truths of a query's hypotheses, in order, and of its goal, at
the values read from a model, contradict (`model::report`): the first
hypothesis that is false, or else the goal, if it is true; none if
neither. A truth that the evaluator does not know is none. -/
def contradiction? (hyps : Array (Name × Option Bool)) (goal : Option Bool) : Option Contradiction :=
  match hyps.find? (·.2 == some false) with
  | some (h, _) => some (.hypothesis h)
  | none => if goal == some true then some .goal else none

/-- Whether the readers of both front ends misread every integer of a
model that a check reports as one more than it is, a bug that the ui tests inject, with
the environment variable `FREN_MISREAD_MODELS`, to see that confirmation
catches it (`Reqs/Models#testing`). -/
def misreadModels : BaseIO Bool := return (← IO.getEnv "FREN_MISREAD_MODELS").isSome

/-- Why a check failed or was inconclusive. -/
inductive Detail where
  | none
  /-- The model that the check would report, read as `vals`, is not a
  counterexample or witness in Fren's semantics (`model::report`). -/
  | refuted (how : Contradiction) (vals : Assignment)
  /-- The procedure's assumptions contradict each other. -/
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

/-- Shared reason for a recursive model that real evaluation does not confirm. -/
def recursiveReason (names : Array Name) : String :=
  "recursive contracts: " ++ ", ".intercalate ((names.toList.eraseDups.mergeSort (fun a b => showPath a < showPath b)).map fun n => s!"`{showPath n}`")

/-- A variant of an enumeration: its constructor, as Fren writes it in a
value (`E::C`), and how many values its payload has. -/
structure Variant where
  name : String
  arity : Nat
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What a set of guarantees forces an output to (`check::forcing`): a whole
value, as Fren writes it, or only its variant. -/
inductive Forced where
  | value (v : String)
  | variant (k : Variant)
  deriving Inhabited, BEq, DecidableEq, Repr

/-- At a realizability conflict, a guarantee of the minimal core and the
rest of the core force an output to different values on the conflict's
input, or to values of different variants (`check::clash_notes`). -/
structure Clash where
  /-- The guarantee, where the note is. -/
  guarantee : Name
  /-- The other guarantees of the core, in its order. -/
  rest : Array Name
  output : Name
  /-- What `guarantee` forces `output` to. -/
  forced : Forced
  /-- What `rest` forces `output` to. -/
  restForced : Forced
  deriving Inhabited

/-- Source member paths use the language's separators, including dotted
annotation segments, without Lean identifier escaping. -/
def showAnnotationPath (name : Name) : String :=
  "::".intercalate (name.components.map (·.toString (escape := false)))

/-- A Boolean source group whose alternatives are retained for conflict
explanations, without replacing its owning constraint in a primary core. -/
inductive BranchKind where
  | disjunction
  | equivalence
  | exactlyOne
  deriving Inhabited, BEq, DecidableEq, Repr

/-- A source member's final logical identity and formula. Leading guards
are already included; a group's formulas exactly reconstruct its owner. -/
structure BranchMember (F : Type) where
  name : Name
  formula : F
  valueFormula? : Option F := none
  evaluationGuard? : Option F := none
  range? : Option Range := none
  text : String := ""
  deriving Inhabited, BEq

structure BranchGroup (F : Type) where
  owner : Name
  kind : BranchKind
  guard? : Option F := none
  members : Array (BranchMember F)
  deriving Inhabited, BEq

/-- Change the backend formula representation while preserving source identity. -/
def BranchMember.map (f : F → G) (member : BranchMember F) : BranchMember G :=
  { name := member.name, formula := f member.formula, valueFormula? := member.valueFormula?.map f,
    evaluationGuard? := member.evaluationGuard?.map f, range? := member.range?, text := member.text }

def BranchGroup.map (f : F → G) (group : BranchGroup F) : BranchGroup G :=
  { owner := group.owner, kind := group.kind, members := group.members.map (·.map f), guard? := group.guard?.map f }

/-- Source observations are distinct from conflict alternatives: a group
under negation has observations too, while its alternatives need not be
those of a positive disjunction. -/
structure MemberGroup (F : Type) where
  owner : Name
  op : String
  wanted : Bool := true
  members : Array (BranchMember F)
  deriving Inhabited, BEq

def MemberGroup.map (f : F → G) (group : MemberGroup F) : MemberGroup G :=
  { owner := group.owner, op := group.op, wanted := group.wanted, members := group.members.map (·.map f) }

/-- An observation in the actual primary model. None means unknown;
false evaluation status means the member was deliberately not evaluated. -/
structure MemberValue where
  owner : Name
  op : String
  name : Name
  evaluated? : Option Bool := none
  value? : Option Bool := none
  range? : Option Range := none
  text : String := ""
  deriving Inhabited, BEq

/-- A member whose opposite polarity follows from the other constraints.
`rest` is minimized under the fixed hypotheses, never under the
contradictory complete alternative. -/
structure BranchOpposition where
  member : Name
  wanted : Bool
  rest : Array Name
  range? : Option Range := none
  text : String := ""
  deriving Inhabited

/-- A conditional conflict, with the alternative kept separate from its
minimal core. An impossible alternative never claims to force a value. -/
structure BranchCaseConflict where
  name : Name
  label : String := ""
  excluded : Bool := false
  impossible : Bool := false
  core : Array Name := #[]
  clashes : Array Clash := #[]
  opposed : Array BranchOpposition := #[]
  range? : Option Range := none
  text : String := ""
  deriving Inhabited

structure BranchConflict where
  owner : Name
  kind : BranchKind
  cases : Array BranchCaseConflict
  premises : Array Name := #[]
  constraints : Array Name := #[]
  condition? : Option Name := none
  deriving Inhabited

structure CheckResult where
  kind : CheckKind
  comp : Name
  /-- The constraint checked, the call, or the `det` variable; `none` for
  checks of a whole comp. -/
  prop? : Option Name
  /-- For `inst`: the called procedure, and its assumption checked; for
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
  explanationPremises : Array Name := #[]
  /-- Conditional explanations for disjunctions in the primary core. -/
  branchConflicts : Array BranchConflict := #[]
  memberValues : Array MemberValue := #[]
  /-- Decided by enumeration only up to this size bound, not for every
  behaviour (`check::enumerated_verdict`). -/
  bounded? : Option Nat := none
  /-- For `realizable`, of the contract of a generic function without a
  body, checked for every type (`Comp.generic`). -/
  generic : Bool := false
  /-- Of a global expectation with a block, whose messages speak of its
  expectations, assumptions and calls rather than of guarantees; set by the
  front ends where they report it. -/
  global : Bool := false
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
  /-- Read a formula from the actual returned model, without a fresh query.
  An unavailable snapshot reports unknown, never a guessed truth. -/
  modelBool? : Option (Array (Name × V) → F → m (Option Bool)) := none
  falseF : F
  notF : F → F
  conj : Array F → F
  /-- `∃ outputs, f`, over the procedure's outputs. -/
  existsOutputs : F → m F
  /-- `x = v` for variable `x`, if `v` can be used in a formula. -/
  pin : Name → V → m (Option F)
  /-- The variant of `v`, a value of the variable `x` whose type is an
  enumeration, with the formula that `x` is of that variant, its tester;
  none if `x`'s type is not an enumeration, or the formula cannot be
  built. -/
  pinVariant : Name → V → m (Option (Variant × F))
  /-- `v`, written the way Fren writes values. -/
  render : Name → V → m String
  /-- What the model of the query of the hypotheses and the goal, a
  counterexample or witness that a check reports, contradicts, evaluated in
  Fren's semantics at the values that `render` shows; none if it confirms
  the answer or leaves it undecided (`Reqs/Models#confirmation`). -/
  confirm? : Option (Array (Name × F) → F → Array (Name × V) → m (Option Contradiction)) := none
  /-- `f` with each variable `x` that is not an own parameter (call variables
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
  /-- A `det` variable. -/
  isDet : Bool := false
  deriving Inhabited

/-- Universally quantified: not chosen by the procedure (`Role.isUniversal`). -/
def VarSig.isIn (v : VarSig) : Bool := v.role.isUniversal

/-- The name of the second copy of variable `n`, for `determinism`. Never a
Fren identifier, so it cannot clash. -/
def primed (n : Name) : Name := n.appendAfter "'"

/-- A call, with formulas over the calling procedure's variables. -/
structure Inst (F : Type) where
  name : Name
  comp : Name
  bindings : F
  /-- The called procedure's assumptions, requirements and calls. -/
  behaviour : F
  /-- The called procedure's assumptions, each an obligation, after the
  constraints of its inputs' types (`Reqs/Check#call-assumptions`). -/
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
  /-- A binding of the call at this position. -/
  | binding (k : Nat)
  /-- The body or a postcondition of a function, or the value of a
  constant: the function's preconditions, and the conditions around it,
  which its goal already has. -/
  | body
  deriving Inhabited, BEq, Repr

/-- An index `q[i]` of a constraint, with the formula that it is in range
where it is evaluated: its guard implies its bounds. -/
structure IndexSite (F : Type) where
  /-- The constraint, the defined output, or the call whose binding it is in. -/
  prop : Name
  /-- Which index of it, in order. -/
  k : Nat
  place : IndexPlace
  goal : F
  /-- For a value given where a pattern type is declared, rather than an
  index: that type, as written (`Reqs/Check#pattern-types`). -/
  patTy? : Option String := none
  /-- Distributed Boolean clauses cannot justify their own evaluation sites. -/
  excludeSelf : Bool := false
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

/-- A procedure, with its items as backend formulas over its variables. -/
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
  /-- Some variable's type, its own or a call's, is or contains an
  abstract type. -/
  typesInterpreted : Bool := false
  /-- A declaration checks existence in every interpretation. With no variable
  interpretation, a direct satisfiability witness answers the same question. -/
  inhabitation : Bool := false
  /-- The questions about the cases of its tables and `match`es, and about
  the arguments of its applications of functions with preconditions. -/
  tables : Array (TableSite F) := #[]
  /-- For the body of a defined function: its postconditions, each a claim
  over its parameters (`check::postcondition`); its preconditions are its
  `assumes`. -/
  posts : Array (Name × F) := #[]
  /-- This function is checked by simultaneous Hoare induction. -/
  recursive : Bool := false
  /-- For the body or contract of a function: the function, which the
  results of `postcondition` name. -/
  fn? : Option Name := none
  /-- For the contract of a generic function without a body: it is checked
  once, at its type parameters, for every type (`F0653`). -/
  generic : Bool := false
  /-- Source Boolean groups, whose owners match named assumptions or requirements. -/
  branchGroups : Array (BranchGroup F) := #[]
  memberGroups : Array (MemberGroup F) := #[]

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

/-- Whether `hyps` force the variable `x` to `v`'s variant, where `v` is
its value in a model of them: that `x` is of that variant follows from
them (`check::forcing`). A variant that cannot be pinned is not known to
be forced. -/
def forcesVariant (hyps : Array (Name × F)) (x : Name) (v : V) : m Bool := do
  let some (_, f) ← b.pinVariant x v | return false
  return (← b.query hyps f false).isUnsat

/-- What `hyps` force the variable `x` to, where `v` is its value in a model
of them and `k?` the variant of `v`: the value `v`, rendered as `s`, if it
is forced (`forces`); else its variant, if that is forced
(`forcesVariant`); else nothing (`check::forcing`). -/
def forcedOf (hyps : Array (Name × F)) (x : Name) (v : V) (s : String) (k? : Option Variant) : m (Option Forced) := do
  if ← forces b hyps x v then return some (.value s)
  let some k := k? | return none
  if ← forcesVariant b hyps x v then return some (.variant k)
  return none

/-- The clash at the guarantee `e` of the core `core`, under the fixed
hypotheses `pinned`: the first of the outputs `outs` that `{e}` and the
rest of the core force to different values, or to values of different
variants (`check::clash_notes`). Each side is asked for a model, then
whether each output's value in it follows (`forces`); only the outputs
whose values in the two models differ are asked about, since sides that
force an output both force its value in their models. Where the two
values have the same variant, or either has none, only a clash of whole
values is looked for; where their variants differ, each side forces the
output's whole value or, failing that, its variant (`forcedOf`), so a
clash of whole values is preferred to one of variants. None if the rest
is empty, which forces nothing, or a side has no model. -/
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
    let k₁ := (← b.pinVariant o v₁).map (·.1)
    let k₂ := (← b.pinVariant o v₂).map (·.1)
    -- Of the same variant, or of none: only whole values can clash.
    let variants := k₁.isSome && k₂.isSome && k₁ != k₂
    let some f₁ ← forcedOf b (pinned ++ one) o v₁ s₁ (if variants then k₁ else none) | continue
    let some f₂ ← forcedOf b (pinned ++ rest) o v₂ s₂ (if variants then k₂ else none) | continue
    return some { guarantee := e, rest := rest.map (·.1), output := o, forced := f₁, restForced := f₂ }
  return none

/-- Whether `found` notes leave room for another under the budget
`examples`, `none` for no limit (`check::clash_notes`). -/
def withinBudget (found : Nat) : Option Nat → Bool
  | none => true
  | some n => found < n

/-- The clashes under fixed hypotheses `pinned`, one at most at each
guarantee of `core`, in its order, and at most `examples` in all
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

/-- The verdict `verdict` and the detail `d`, which reports `vals`, the
values that `model` of the query of `hyps` and `goal` gives, unless Fren's
semantics at those values contradicts the solver (`model::report`): then the
check is inconclusive, and its detail says what the values contradict. -/
def confirmReport (hyps : Array (Name × F)) (goal : F) (model : Array (Name × V)) (vals : Assignment)
    (verdict : Verdict) (d : Detail) : m (Verdict × Detail) := do
  let some confirm := b.confirm? | return (verdict, d)
  match ← confirm hyps goal model with
  | some how => return (.inconclusive, .refuted how vals)
  | none => return (verdict, d)

/-- The variables of `model` that are universally quantified, and not also
outputs, for a realizability conflict. -/
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

/-- The assumptions, then what each call contributes (`I`). -/
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

/-- The SAT shortcut is only a fresh-output declaration carrier, never a
procedure whose inputs, definitions, assumptions or calls need the ordinary
universal-completion protocol. Interpretation freedom is checked separately. -/
def Comp.fixedInhabitation (c : Comp F) (interprets : F → Bool := fun _ => false) : Bool :=
  c.inhabitation && !c.realizableInterpreted interprets && c.defs.isEmpty &&
    c.assumes.isEmpty && c.insts.isEmpty && c.vars.all (·.role == .output)

/-- Additional all-model forcing relationships under the general assumptions
and calls. The primary core may be input-local; its pins are not premises. -/
def conflictClashes (c : Comp F) (base : Array (Name × F)) (core : Array Name)
    (examples : Option Nat) (interprets : F → Bool) : m (Array Clash) :=
  if c.realizableInterpreted interprets then pure #[]
  else clashesOf b base ((c.substHyps b c.reqs).filter (core.contains ·.1)) c.clashOutputs examples

/-- One alternative of a source group. Equivalence always has the two
alternatives all-hold and none-hold, rather than a parity chain. -/
structure BranchAlternative (F : Type) where
  name : Name
  formula : F
  label : String := ""
  wanted? : Option Bool := none
  memberWanted : Array (Name × Bool) := #[]
  range? : Option Range := none
  text : String := ""

def BranchGroup.alternatives (group : BranchGroup F) : Array (BranchAlternative F) :=
  let cases : Array (BranchAlternative F) := match group.kind with
  | .disjunction => group.members.map fun member =>
    { name := member.name, formula := member.formula, range? := member.range?, text := member.text }
  | .exactlyOne => group.members.map fun chosen =>
    { name := chosen.name, formula := b.conj (group.members.map fun member =>
        if member.name == chosen.name then member.formula else b.notF member.formula)
      label := "only " ++ showAnnotationPath chosen.name ++ " holds"
      memberWanted := group.members.map fun member => (member.name, member.name == chosen.name)
      range? := chosen.range?, text := chosen.text }
  | .equivalence =>
    let operands := if group.members.size == 2 then "both operands" else "all operands"
    #[{ name := .str group.owner "all", formula := b.conj (group.members.map (·.formula))
        label := operands ++ " are true", wanted? := some true },
      { name := .str group.owner "none", formula := b.conj (group.members.map (b.notF ·.formula))
        label := operands ++ " are false", wanted? := some false }]
  cases.map fun alternative =>
    { alternative with formula := group.guard?.map (fun guard =>
        b.notF (b.conj #[guard, b.notF alternative.formula])) |>.getD alternative.formula }

/-- Explain only owners in an already minimized core. Conditional cores
keep the selected alternative as a fixed hypothesis, so dropping other
alternatives never changes or masquerades as the unconditional core.
A model of each forcing side is required before any pin/polarity query. -/
def branchConflictsOf (groups : Array (BranchGroup F)) (fixed candidates : Array (Name × F))
    (core : Array Name) (outs : Array Name) (examples : Option Nat)
    (valuesSafe : Bool := true) (premises? : Option (Array Name) := none)
    (condition? : Option Name := none) : m (Array BranchConflict) := do
  let mut found := #[]
  let mut inspected := 0
  for group in groups do
    if !core.contains group.owner then continue
    if !withinBudget inspected examples then break
    inspected := inspected + 1
    let base := fixed.filter (·.1 != group.owner)
    let rest := candidates.filter fun (n, _) => core.contains n && n != group.owner
    -- A contradiction in the premises is not an explanatory relationship.
    if (← b.query (base ++ rest) b.falseF false).answer != .sat then continue
    let mut cases := #[]
    for alternative in group.alternatives b do
      let branch := #[(alternative.name, alternative.formula)]
      let excluded ← b.query (base ++ branch ++ rest) b.falseF false
      if !excluded.isUnsat then
        cases := cases.push { name := alternative.name, label := alternative.label
                              range? := alternative.range?, text := alternative.text }
        continue
      let conditional ← minimize b (base ++ branch) rest b.falseF
      let branchModel ← b.query (base ++ branch) b.falseF true
      let impossible := branchModel.isUnsat
      let mut clashes := #[]
      if valuesSafe && !impossible then
        if let some clash ← clashAt b base (branch ++ rest) outs alternative.name then
          clashes := clashes.push clash
      let mut opposed := #[]
      if alternative.wanted?.isSome || !alternative.memberWanted.isEmpty then
        -- The shared query above already established consistency.
        for member in group.members do
          let wanted := alternative.wanted?.getD ((alternative.memberWanted.find? (·.1 == member.name)).map (·.2) |>.getD true)
          let opposite := if wanted then b.notF member.formula else member.formula
          if (← b.query (base ++ rest) opposite false).isUnsat then
            let because ← minimize b base rest opposite
            opposed := opposed.push { member := member.name, wanted, rest := because
                                      range? := member.range?, text := member.text }
      cases := cases.push { name := alternative.name, label := alternative.label, excluded := true
                            impossible, core := conditional, clashes, opposed
                            range? := alternative.range?, text := alternative.text }
    if cases.any (·.excluded) then
      found := found.push { owner := group.owner, kind := group.kind, cases
                            premises := (premises?.getD (fixed.map (·.1))).filter (· != group.owner)
                            constraints := rest.map (·.1), condition? }
  return found

/-- The source groups with the same definition substitution as the primary
realizability query. -/
def Comp.substBranchGroups (c : Comp F) : Array (BranchGroup F) :=
  c.branchGroups.map (·.map (c.subst b .realizable))

/-- `realizable`: every input allowed by the assumptions has outputs
satisfying the requirements, whatever the calls do
(`check::realizability`). Defined outputs are replaced by their
definitions, so that they are never under `∃` (`check::definitions`). A
conflict comes with at most `examples` clashes of forced outputs
(`clashesOf`), `none` for no limit, and none if they would depend on an
interpretation, as `interprets` says of a formula. -/
def checkRealizableUniversal (c : Comp F) (examples : Option Nat := some 1) (interprets : F → Bool := fun _ => false) :
    m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .realizable, comp := c.path, prop? := none, target? := c.fn?.map (·, .anonymous), verdict, detail
      generic := c.generic }
  let sub := c.substHyps b
  let assumes := sub c.assumes
  let assumeQ ← b.query assumes b.falseF false
  -- `cex_q` is asked only if `assume_q` is not `unsat` (`check::realizability_protocol`).
  let cexQ ← if assumeQ.isUnsat then pure (.unknown "not asked")
    else b.query (sub (c.hyps b)) (← b.existsOutputs (c.subst b .realizable (b.conj (c.reqs.map (·.2))))) true
  let (verdict, reportsCex, reportsVacuous) := realizableVerdict assumeQ.answer cexQ.answer
  if reportsVacuous then
    let core ← minimize b #[] assumes b.falseF
    let branches ← branchConflictsOf b (c.substBranchGroups b) #[] assumes core
      ((c.vars.filter (·.isPub)).map (·.name)) examples (!c.realizableInterpreted interprets)
    return { result verdict (.vacuousAssumptions core) with branchConflicts := branches }
  if reportsCex then
    let .sat model := cexQ | return result verdict
    let input := conflictInput c.vars model
    let pinned ← pins b input
    let core ← minimize b pinned (sub c.reqs) b.falseF
    let base := sub (c.hyps b)
    let clashes ← conflictClashes b c base core examples interprets
    let branches ← branchConflictsOf b (c.substBranchGroups b) base (sub c.reqs) core c.clashOutputs examples
      (!c.realizableInterpreted interprets)
    return { result verdict (.conflict (← renderModel b c.vars input fun v => v.isIn && v.isPub) core)
             with clashes, explanationPremises := base.map (·.1), branchConflicts := branches }
  if verdict == .inconclusive then
    return result verdict (.unknown (if cexQ.reason.isEmpty then assumeQ.reason else cexQ.reason))
  return result verdict

/-- Declaration inhabitation uses SAT only for the validated fixed carrier;
all other shapes keep the universal-input realizability protocol. -/
def checkRealizable (c : Comp F) (examples : Option Nat := some 1) (interprets : F → Bool := fun _ => false) :
    m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .realizable, comp := c.path, prop? := none, target? := c.fn?.map (·, .anonymous), verdict, detail
      generic := c.generic }
  if c.fixedInhabitation interprets then
    let fixed := c.defEqs .realizable ++ c.hyps b
    let q ← b.query (fixed ++ c.reqs) b.falseF true
    match q with
    | .sat _ => return result .pass
    | .unsat =>
      let core ← minimize b fixed c.reqs b.falseF
      return result .fail (.conflict #[] core)
    | .unknown reason => return result .inconclusive (.unknown reason)
  checkRealizableUniversal b c examples interprets

/-- `inst`: an assumption of call `k`'s procedure follows from the
assumptions, `k`'s bindings and the earlier calls
(`check::instance_assumption`). -/
def checkInst (c : Comp F) (k : Nat) (i : Inst F) (a : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .inst, comp := c.path, prop? := some i.name, target? := some (i.comp, a.1), verdict, detail
      patTy? := (i.typed.find? (·.1 == a.1)).map (·.2) }
  let hyps := c.defEqs .inst ++ (c.hyps b k).push (i.name, i.bindings)
  let q ← b.query hyps a.2 true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    -- Inputs and earlier calls; later ones (and `i`) are unconstrained.
    let later := (c.insts.extract k).map (·.name)
    let shown v := v.isIn && v.isPub && !later.contains v.name.getRoot
    let vals ← renderModel b c.vars model shown
    let (verdict, detail) ← confirmReport b hyps a.2 model vals verdict (.counterexample vals)
    return result verdict detail
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- Observe only evaluated members in the primary model. In particular,
this never substitutes another interpretation via a second solver query. -/
def captureMembers (c : Comp F) (owner : Name) (model : Array (Name × V)) : m (Array MemberValue) := do
  let some read := b.modelBool? | return #[]
  let mut values := #[]
  for group in c.memberGroups.filter (·.owner == owner) do
    for member in group.members do
      let evaluated ← match member.evaluationGuard? with
        | none => pure (some true)
        | some guard => read model guard
      let value ← if evaluated == some true then read model (member.valueFormula?.getD member.formula) else pure none
      values := values.push {
        owner := owner
        op := group.op
        name := member.name
        evaluated? := evaluated
        value? := value
        range? := member.range?
        text := member.text
      }
  return values

/-- `expect`: the expectation follows from the assumptions, calls and
requirements (`check::expectation`). -/
def checkExpect (c : Comp F) (e : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .expect, comp := c.path, prop? := some e.1, verdict, detail }
  let hyps := c.defEqs .expect ++ (c.hyps b ++ c.reqs)
  let q ← b.query hyps e.2 true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    let vals ← renderModel b c.vars model (·.isPub)
    let (verdict, detail) ← confirmReport b hyps e.2 model vals verdict (.counterexample vals)
    return { result verdict detail with memberValues := ← captureMembers b c e.1 model }
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- `cover`: some behaviour satisfying the assumptions, calls and
requirements satisfies the cover goal, which a model of the negated goal
witnesses (`check::cover_goal`). -/
def checkCover (c : Comp F) (g : Name × F) (examples : Option Nat := some 1) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .cover, comp := c.path, prop? := some g.1, verdict, detail }
  let hyps := c.hyps b ++ c.reqs
  let goal := b.notF g.2
  let q ← b.query (c.defEqs .cover ++ hyps) goal true
  match coverVerdict q.answer, q with
  | (verdict, true, _), .sat model =>
    let vals ← renderModel b c.vars model (·.isPub)
    let (verdict, detail) ← confirmReport b (c.defEqs .cover ++ hyps) goal model vals verdict (.witness vals)
    return { result verdict detail with memberValues := ← captureMembers b c g.1 model }
  -- The core is sought only on `unsat` (`Reqs/Check#cover-goals`).
  | (verdict, _, true), _ =>
    let core ← minimize b (c.defEqs .cover) hyps goal
    let fixed := c.defEqs .cover ++ c.hyps b ++ #[(g.1.appendAfter "_goal", g.2)]
    let branches ← branchConflictsOf b c.branchGroups fixed hyps core
      ((c.vars.filter (·.isPub)).map (·.name)) examples (!c.typesInterpreted)
      (some ((c.defEqs .cover ++ c.hyps b).map (·.1))) (some g.1)
    return { result verdict (.vacuous core) with branchConflicts := branches }
  | (.inconclusive, _, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _, _), _ => return result verdict

/-- The hypotheses of an index's place, for `definedness`. -/
def Comp.siteHyps (c : Comp F) (b : Backend m F V) (site : IndexSite F) : Array (Name × F) :=
  let own (name : Name) := name == site.prop || (site.excludeSelf &&
    (name.toString (escape := false)).startsWith (site.prop.toString (escape := false) ++ "."))
  match site.place with
  | .assume => c.assumes.filter (!own ·.1)
  | .binding k => c.hyps b k
  | .prop => c.hyps b ++ (if site.excludeSelf then c.reqs.filter (!own ·.1) else c.reqs)
  | .body => c.assumes

/-- `definedness`: the index is in range wherever it is evaluated, given the
hypotheses of its place (`check::definedness`): for an assumption, the
other assumptions; for a binding, the assumptions and earlier calls;
otherwise the assumptions, calls and requirements. -/
def checkDefinedness (c : Comp F) (site : IndexSite F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .definedness, comp := c.path, prop? := some site.prop, index? := some site.k, verdict, detail
      patTy? := site.patTy? }
  let hyps := c.defEqs .definedness ++ c.siteHyps b site
  let q ← b.query hyps site.goal true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    let vals ← renderModel b c.vars model (·.isPub)
    let (verdict, detail) ← confirmReport b hyps site.goal model vals verdict (.counterexample vals)
    return result verdict detail
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
q: y = 1` (`check::reachability`). A binding's own call is never
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
    let vals ← renderModel b c.vars model (·.isPub)
    let (verdict, detail) ← confirmReport b (c.tableHyps b t) t.site.goal model vals verdict (.counterexample vals)
    return result verdict detail
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- `postcondition`: the postcondition `p` of a defined function, named
after the function and the clause, follows from its preconditions, its
parameters free (`check::postcondition`); for a structural recursion, by
simultaneous Hoare induction with facts at actual applications. -/
def checkPostcondition (c : Comp F) (p : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .postcondition, comp := c.path, prop? := some p.1, target? := c.fn?.map (·, Name.mkSimple p.1.getString!),
      verdict, detail }
  let q ← b.query (c.assumes) p.2 true
  match expectVerdict q.answer, q with
  | (verdict, true), .sat model =>
    let vals ← renderModel b c.vars model (·.isPub)
    let (verdict, detail) ← confirmReport b c.assumes p.2 model vals verdict (.counterexample vals)
    return result verdict detail
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
def checkVacuity (c : Comp F) (t : Name × F) (examples : Option Nat := some 1) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .vacuity, comp := c.path, prop? := some t.1, verdict, detail }
  let hyps := c.hyps b ++ c.reqs
  let goal := b.notF t.2
  let q ← b.query (c.defEqs .vacuity ++ hyps) goal (c.memberGroups.any (·.owner == t.1))
  match vacuityVerdict q.answer with
  | .fail =>
    let core ← minimize b (c.defEqs .vacuity) hyps goal
    let fixed := c.defEqs .vacuity ++ c.hyps b ++ #[(t.1.appendAfter "_trigger", t.2)]
    let branches ← branchConflictsOf b c.branchGroups fixed hyps core
      ((c.vars.filter (·.isPub)).map (·.name)) examples (!c.typesInterpreted)
      (some ((c.defEqs .vacuity ++ c.hyps b).map (·.1))) (some t.1)
    return { result .fail (.vacuous core) with branchConflicts := branches }
  | .inconclusive => return result .inconclusive (.unknown q.reason)
  | .pass =>
    let members ← match q with | .sat model => captureMembers b c t.1 model | _ => pure #[]
    return { result .pass with memberValues := members }

/-- `redundancy`: the assumption or requirement `p` does not follow from
`others`: for an assumption, the other assumptions; for a requirement, the
assumptions, calls and other requirements (`check::non_redundancy`). -/
def checkRedundant (c : Comp F) (others : Array (Name × F)) (p : Name × F) : m CheckResult := do
  let result (verdict : Verdict) (detail : Detail := .none) : CheckResult :=
    { kind := .redundancy, comp := c.path, prop? := some p.1, verdict, detail }
  let q ← b.query (c.defEqs .redundancy ++ others) p.2 false
  match vacuityVerdict q.answer with
  | .fail => return result .fail (.redundant (← minimize b (c.defEqs .redundancy) others p.2))
  | .inconclusive => return result .inconclusive (.unknown q.reason)
  | .pass => return result .pass

/-- `determinism`: any two behaviours satisfying the assumptions, calls
and requirements on the same input agree on the `det` variable `x`
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
    let d := .nondeterministic input (← modelValue b x model x) (← modelValue b x model (primed x))
    let (verdict, detail) ← confirmReport b twice (b.samePrimed x) model input verdict d
    return result verdict detail
  | (.inconclusive, _), _ => return result .inconclusive (.unknown q.reason)
  | (verdict, _), _ => return result verdict

/-- The checks of a global expectation (`check::applies`), as a `Comp`:
those of a procedure, but for redundancy and determinism, since it
constrains nothing; with no outputs, its realizability is that its
assumptions are satisfiable (`Reqs/Lang/Global#meaning`). -/
def globalKinds : Array CheckKind :=
  #[.realizable, .inst, .expect, .cover, .vacuity, .definedness, .completeness, .disjointness, .precondition,
    .reachability]

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

/-- The checks run on a global expectation if `global`, else on a procedure
(`check::applies`). -/
def kindsFor (global : Bool) : Array CheckKind :=
  if global then globalKinds else CheckKind.all

/-- What the checks run on (`check::CheckedItem`). -/
inductive CheckedItem where
  | component
  | global
  /-- A global expectation in the short form, `expect n: e`, which has no
  assumptions to satisfy. -/
  | shortGlobal
  /-- The body and contract of a function, or the value of a constant. -/
  | body
  /-- The contract of an uninterpreted function with postconditions. -/
  | contract
  deriving Inhabited, DecidableEq, Repr

/-- The checks run on an item (`check::applies`). -/
def CheckedItem.kinds : CheckedItem → Array CheckKind
  | .component => kindsFor false
  | .global => kindsFor true
  | .shortGlobal => (kindsFor true).filter (· != .realizable)
  | .body => bodyKinds
  | .contract => contractKinds

/-- The SMT-LIB logic of a check's queries (`cli::logic`): realizability
quantifies, over outputs, and so does every query of a spec with an
unbounded quantifier (`quantified`); a spec that uses strings or sets
(`extended`) needs `ALL`, and one that projects a relation over a type that
is not finite (`projection`), `HO_ALL`. -/
def logic (kind : CheckKind) (extended : Bool := false) (projection : Bool := false) (quantified : Bool := false) :
    String :=
  if extended then (if projection then "HO_ALL" else "ALL") else match kind with
    | .realizable => "UFDTLIA"
    | _ => if quantified then "UFDTLIA" else "QF_UFDTLIA"

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


/-- The cvc5 option for the contract of a generic function without a body,
checked once at its type parameters' sorts
(`Reqs/Lang/GenericFunctions#uninterpreted-generic-functions`):
`finite-model-find`, with which cvc5 finds the small domains, such as one
of a single value, on which the contract may fail, rather than giving up. -/
def finiteModelOptions : List (String × String) := [("finite-model-find", "true")]

/-- The checks reported of the contract of a generic function without a
body (`lang::generic_contract`), from its check at its type parameters'
sorts, `atSorts`, and, where that does not pass, its check at each instance
that the spec applies, `instances`, which `fren` and the hosted front end
run only then: the opaque check if it passes or the spec applies no
instance, and otherwise each instance's. -/
def genericContract {α : Type} (verdict : α → Verdict) (atSorts : α) (instances : Array α) : Array α :=
  match verdict atSorts with
  | .pass => #[atSorts]
  | _ => if instances.isEmpty then #[atSorts] else instances

/-- `inst` for each assumption of each call, in order. -/
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

/-- `determinism` for each `det` variable. -/
def checkDets (c : Comp F) : m (Array CheckResult) :=
  c.vars.filterMapM fun v => do
    if v.isDet then return some (← checkDeterminism b c v.name)
    return none

/-- The results of `x` if `selected`, else none. -/
def ifSelected (selected : Bool) (x : m (Array α)) : m (Array α) := if selected then x else pure #[]

/-- All selected checks for one procedure, in reporting order, each with the
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
  let covers ← ifSelected (kinds.contains .cover) (c.covers.mapM (fun g => checkCover (bk .cover) c g examples))
  let vacuities ← ifSelected (kinds.contains .vacuity) (c.triggers.mapM (fun t => checkVacuity (bk .vacuity) c t examples))
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

/-- Finalize simultaneous induction after counterexamples have been confirmed.
A clause that used an unproved sibling's hypotheses is not a reported success. -/
def recursiveResults (recursive : Bool) (results : Array CheckResult) : Array CheckResult :=
  let unproved := results.any fun r => r.kind == .postcondition && r.verdict != .pass
  results.map fun r =>
    if recursive && r.kind == .postcondition && r.verdict == .pass && !recursivePostResult true unproved then
      { r with verdict := .inconclusive, detail := .unknown "another postcondition used by simultaneous induction did not pass" }
    else r

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
application that it does not mention, as of a called procedure's
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

/-- The procedure that checks the realizability of the contract of the
uninterpreted function `f` (`Reqs/Check#contracts-of-uninterpreted-functions`),
whose path is its module `path`: its parameters `params` as inputs, its
value `value` as its one output, and its preconditions `pres` and
postconditions `posts`, of the value, as its assumptions and guarantees,
with `sites`, the questions about the tables and applications in its
clauses. Both front ends check this procedure. -/
def contractComp (path f : Name) (params : Array Name) (value : Name) (pres posts : Array (Name × F))
    (sites : Array (TableSite F) := #[]) (generic : Bool := false) : Comp F :=
  { path, vars := params.map (fun x => { name := x, role := .input, isPub := true }) |>.push
      { name := value, role := .output, isPub := true }
    assumes := pres, reqs := posts, expects := #[], triggers := #[], tables := sites, fn? := some f, generic }

/-- The formulas of the query of the cover goal `g` (`checkCover`): the
definitions, the assumptions, each call's bindings and the meaning of
its procedure, the requirements, and the goal. No expectation or other
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

/-- A model that Fren's semantics contradicts is an internal error, so an
error (`model::report`). -/
def CheckResult.severity? (r : CheckResult) : Option Severity :=
  if r.detail matches .refuted .. then some .error else Fren.Core.severity? r.kind r.verdict

/-- The most severe of the severities of a run's results, `none` if there
are none, for the exit code (`cli::worst_severity`). -/
def worst (sevs : Array Severity) : Option Severity :=
  if sevs.any (· == .error) then some .error
  else if sevs.any (· == .warning) then some .warning
  else none

structure Message where
  severity : Severity
  /-- The procedure item the message is about, or `none` for the procedure itself. -/
  item? : Option Name
  /-- Point at the item's `when`/`unless` condition rather than its name. -/
  atTrigger : Bool := false
  /-- Point at the item's index with this number, in order, rather than its name. -/
  atIndex? : Option Nat := none
  /-- Point at the place of the item's question about its tables with this
  number, in order, rather than its name. -/
  atSite? : Option Nat := none
  /-- Explicit source member range for a Boolean block explanation. -/
  atRange? : Option Range := none
  msg : Msg
  deriving Inhabited

def Message.text (m : Message) : String := m.msg.text

def showNames (ns : Array Name) : String :=
  ", ".intercalate (ns.toList.map fun n => s!"`{n.toString (escape := false)}`")

def showAssignment (a : Assignment) : String :=
  if a.isEmpty then "(any values)" else ", ".intercalate (a.toList.map fun (n, v) => s!"{n} = {v}")

/-- `` `a`, `b` and `c` ``: names in prose. -/
def showNamesAnd (ns : Array Name) : String :=
  match ns.toList.map (fun n => s!"`{n.toString (escape := false)}`") |>.reverse with
  | [] => ""
  | [n] => n
  | last :: rest => s!"{", ".intercalate rest.reverse} and {last}"

/-- The note of a realizability conflict (`Reqs/View#check-results`): the
input, or the arguments of a function (`what`), one variable to a line,
and then what no outputs satisfy, `unmet`. -/
def conflictNote (what : String) (input : Assignment) (unmet : String) : String :=
  if input.isEmpty then s!"note: {unmet}"
  else s!"note: for the {what}\n" ++ String.join (input.toList.map fun (n, v) => s!"    {n} = {v}\n") ++ unmet

/-- `, _` for each of `k` values of a payload after its first
(`view::wildcards`). -/
def furtherWildcards (k : Nat) : String := String.join (List.replicate k ", _")

/-- One `_` for each of `arity` values of a payload, separated by `, `,
as a pattern of the variant writes them (`view::wildcards`). -/
def wildcards (arity : Nat) : String := if arity = 0 then "" else "_" ++ furtherWildcards (arity - 1)

/-- The wildcards of what a clash note says is forced: of its variant's
payload, and none of a value (`view::clash_text`). -/
def Forced.blanks : Forced → String
  | .value _ => ""
  | .variant k => wildcards k.arity

/-- The variant `k` as a pattern that its values match: `E::C` without a
payload, else `E::C(_)`, with one `_` for each value of the payload
(`view::clash_text`). -/
def Variant.pattern (k : Variant) : String :=
  if k.arity = 0 then k.name else s!"{k.name}({wildcards k.arity})"

/-- What a clash note says is forced of the output `o` (`view::clash_text`):
`o = v` of a whole value `v`, and `o is P` of a variant, `P` the pattern
of its values. -/
def forcedText (o : String) : Forced → String
  | .value v => s!"{o} = {v}"
  | .variant k => s!"{o} is {k.pattern}"

/-- The headline of a clash note (`view::clash_text`): the guarantee
`g` forces `f` of the output `o`, and the `count` others of its conflict,
named as the list `others`, force `f'`. -/
def clashLine (g o : String) (f : Forced) (others : String) (f' : Forced) (count : Nat) : String :=
  s!"`{g}` forces {forcedText o f}, but {others}{if count = 1 then " forces " else " force "}{forcedText o f'}"

/-- The headline of a clash note (`Reqs/View#check-results`), at its
guarantee, with the rest of the core named `rest`. -/
def clashText (cl : Clash) (rest : Array Name) : String :=
  clashLine cl.guarantee.getString! (toString cl.output) cl.forced (showNamesAnd rest) cl.restForced rest.size

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
  -- Unescaped, so that an instance of a generic function shows as `pick<Int>`
  -- (`instanceName`).
  "::".intercalate (path.components.map (·.toString (escape := false)))

/-- The subject of the messages about a procedure at `path`, as both front
ends show it: a global expectation, `global`, by its module and the name
of its first expectation, `first?`. -/
def subjectOf (path : Name) (global : Bool) (first? : Option Name) : String :=
  s!"`{showComp (if global then path ++ first?.getD .anonymous else path)}`"

/-- A check's kind, as a message names its check. -/
def kindName : CheckKind → String
  | .realizable => "realizability" | .inst => "call" | .expect => "expectation" | .cover => "cover"
  | .vacuity => "vacuity" | .redundancy => "redundancy" | .determinism => "determinism"
  | .definedness => "definedness" | .completeness => "completeness" | .disjointness => "disjointness"
  | .precondition => "precondition" | .postcondition => "postcondition"
  | .reachability => "reachability"

inductive Advice where
  | raiseTimeout
  | namesConstructs
  deriving Inhabited, BEq, DecidableEq, Repr

/-- What an inconclusive result advises (`view::inconclusive_advice`):
in the decidable core, the solver ran out of time. -/
def inconclusiveAdvice (decidable : Bool) : Advice :=
  if decidable then .raiseTimeout else .namesConstructs

/-- The messages for one result. Passing checks produce none, but for a
cover goal's witness. `decidable` says whether the procedure is in the
decidable core: whether no construct of it opted out. A witness whose query
depends on an interpretation (`CheckResult.interpreted`) is shown without
its values. -/
def baseMessages (hasPrivateOuts : Bool) (r : CheckResult) (decidable : Bool := true) : Array Message :=
  -- A global expectation's `comp` is its module, which may be the root.
  let subject := s!"`{showComp (r.comp ++ (r.prop?.getD .anonymous))}`"
  -- Passes have no severity, and no messages.
  let sev := r.severity?.getD .info
  let one (code : String) (headline : String) (label? : Option String) (notes : Array String)
      (atTrigger := false) (item? := r.prop?) : Message :=
    { severity := sev, item?, atTrigger, atIndex? := r.index?, atSite? := r.site?
      msg := { code? := some code, headline, label?, notes } }
  let priv := if hasPrivateOuts then #["note: private variables are not shown"] else #[]
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
  -- Not a counterexample, nor a witness, but a bug (`Reqs/Models#reporting`).
  | _, .refuted how vals =>
    let what := match how, r.kind with
      | .hypothesis h, _ => s!"makes its hypothesis `{h.toString (escape := false)}` false"
      | .goal, .cover => "makes the cover goal false"
      | .goal, _ => "makes the check's claim true"
    let read := if vals.isEmpty then #[] else #[s!"note: Fren reads the model as {showAssignment vals}"]
    #[{ severity := .error, item? := r.prop?, atIndex? := r.index?, atSite? := r.site?
        msg := { code? := none
                 headline := s!"internal error: the solver's model for the {kindName r.kind} check of {subject} {what} in Fren's semantics"
                 label? := some "model contradicts the solver"
                 notes := read ++ #["note: so it is not shown as a counterexample or a witness, and the check is inconclusive",
                   "note: this is a bug in Fren: in reading the solver's model, or in translating the spec"] } }]
  | .inconclusive, d =>
    let why := match d with | .unknown w => s!": {w}" | _ => ""
    let what := match r.kind, r.target? with
      | .realizable, some (f, _) => s!"the postconditions of `{showComp f}` can hold"
      | .realizable, _ => s!"{subject} is realizable"
      | .inst, some (sub, a) => match r.patTy? with
        | some ty => s!"the parameter `{a.getPrefix}` of `{showComp sub}` has its type `{ty}` for call {subject}"
        | none => s!"the assumption `{a}` of `{showComp sub}` holds for call {subject}"
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
      | .precondition, some (f, p) => s!"the precondition `{p.toString (escape := false)}` of `{showComp f}` holds at an application in {subject}"
      | .precondition, none => s!"a precondition holds at an application in {subject}"
      | .postcondition, some (f, p) => s!"the postcondition `{p.toString (escape := false)}` of `{showComp f}` holds"
      | .postcondition, none => s!"{subject} holds"
      | .reachability, _ => s!"{caseText r.goal?} of {splitText r.goal?} in {subject} can be taken"
    let advice := if let some n := r.bounded? then
        #[s!"note: enumeration searched every behaviour up to size {n}, which does not decide it",
          "help: raise `fren.enumeration.size`, or have the solver check it"]
      else match inconclusiveAdvice decidable with
      | .raiseTimeout => #["note: the solver gave up, so this check neither passed nor failed",
        "help: raise the time limit with `--timeout`, or simplify the constraints involved"]
      | .namesConstructs => #["note: the solver gave up, so this check neither passed nor failed",
        "note: the procedure uses constructs outside the decidable core (`undecidable` is allowed), so the solver may never decide it",
        "help: bring it back into the decidable core, or raise the time limit with `--timeout`"]
    -- An expansion of quantifiers over elements that is too large, or
    -- whose model they refute, has a code of its own.
    match d with
    | .unknown w => if w == "another postcondition used by simultaneous induction did not pass" then
        #[one "F0608" s!"could not decide whether {what}" (some "depends on an unproved postcondition")
          #["note: simultaneous induction used all of the function's postconditions",
            "note: another postcondition failed or was inconclusive, so this check cannot be reported as passed",
            "help: establish the other postconditions before relying on this one"]]
      else if w.startsWith "recursive contracts: " then
        #[one "F0450" s!"could not decide whether {what}" (some "contracts may be too weak")
          #[s!"note: this check fails only under the contracts of {((w.drop 21).toString)}",
            "note: evaluation of the recursive definitions does not confirm the counterexample",
            "help: strengthen those functions' contracts"]]
      else if let some (code, notes) := elementReasonNotes? w then
        #[one code s!"could not decide whether {what}{why}" (some "undecided") notes]
      else #[one "F0608" s!"could not decide whether {what}{why}" (some "undecided") advice]
    | _ => #[one "F0608" s!"could not decide whether {what}{why}" (some "undecided") advice]
  | .fail, .vacuousAssumptions core =>
    if let some (f, _) := r.target? then
      #[one "F0632" s!"the preconditions of `{showComp f}` are unsatisfiable: {showNames (core.map clauseName)} contradict each other"
        (some "no arguments meet its preconditions") #["note: the function could never be applied where its contract says anything",
          "help: weaken or remove one of them"] (item? := none)]
    else
    #[one "F0602" s!"the assumptions of {subject} are unsatisfiable: {showNames core} contradict each other"
      (some "no input satisfies its assumptions")
      #[if r.global then "note: every expectation would hold vacuously" else "note: every guarantee would hold vacuously",
        "help: weaken or remove one of them"] (item? := none)]
  | .fail, .conflict input core =>
    let contract := r.target?.map (·.1)
    let names := if contract.isSome then core.map clauseName else core
    let clashNotes := core.filterMap fun n => do
      let some clash := r.clashes.find? (·.guarantee == n) | none
      let short (ns : Array Name) := if contract.isSome then ns.map clauseName else ns
      let headline := clashText clash (short clash.rest)
      some {
        severity := .info
        item? := some n
        msg := {
          code? := none
          headline := headline
          notes := if r.explanationPremises.isEmpty then #[] else
            #[s!"note: This holds under {showNamesAnd r.explanationPremises}."]
        }
      }
    if let (some f, true) := (contract, r.generic) then
      #[one "F0653" s!"the postconditions of `{showComp f}` cannot all hold at some type" (some "unrealizable contract")
        #[conflictNote "arguments" input s!"no value of `{showComp f}` satisfies {showNamesAnd names}",
          "note: a generic function's contract is checked for every type, where nothing is known of a type parameter's values: they may be equal, and a type may have only one",
          "note: the spec applies it at no instance, where it would be checked instead",
          "help: weaken one of them, or add a precondition that rules these arguments out"] (item? := none)]
      ++ clashNotes
    else
    if let some f := contract then
      #[one "F0631" s!"the postconditions of `{showComp f}` cannot all hold" (some "unrealizable contract")
        #[conflictNote "arguments" input s!"no value of `{showComp f}` satisfies {showNamesAnd names}",
          "note: an uninterpreted function's postconditions are assumed wherever it is applied, so if they cannot hold, every check that applies it would pass",
          "help: weaken one of them, or add a precondition that rules these arguments out"] (item? := none)]
      ++ clashNotes
    else
    -- Call variables (`w.x`) cannot be assumed about.
    let help := if input.all (·.1.isAtomic) then #["help: weaken one of them, or add an `assume` that rules this input out"]
      else #["help: weaken one of them",
        "note: call variables are part of the system: whatever the calls do, the procedure must cope"]
    #[one "F0601" s!"{subject} is not realizable" (some "not realizable")
      (#[conflictNote "input" input s!"no outputs satisfy {showNamesAnd names}"] ++ help) (item? := none)]
    ++ clashNotes
  | .fail, .counterexample vals =>
    if let (.definedness, some ty) := (r.kind, r.patTy?) then
      let m := obligationMsg subject ty (showAssignment vals) priv
      #[one "F0661" m.headline m.label? m.notes]
    else
    if let (.inst, some (sub, a), some ty) := (r.kind, r.target?, r.patTy?) then
      let m := instanceTypeMsg subject (showComp sub) (a.getPrefix.toString) ty (showAssignment vals)
      #[one "F0661" m.headline m.label? m.notes]
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
      #[one "F0629" s!"the precondition `{p.toString (escape := false)}` of `{showComp f}` may not hold at this application in {subject}"
        (some s!"may violate `{showComp f}::{p}`")
        #[s!"counterexample: {showAssignment vals}",
          "note: where a precondition fails, the application's value is unknown, or not what the function is for",
          "help: guard the application, as in `p(x) and f(x) = y`, or assume what the precondition needs"]]
    else
    if let (.postcondition, some (f, p)) := (r.kind, r.target?) then
      #[one "F0630" s!"the postcondition `{p.toString (escape := false)}` of `{showComp f}` does not hold" (some "does not follow from the body")
        #[s!"counterexample: {showAssignment vals}",
          "help: correct the body or the postcondition, or add a precondition that rules this case out"]]
    else
    if let (.inst, some (sub, a)) := (r.kind, r.target?) then
      #[one "F0604" s!"the assumption `{a}` of `{showComp sub}` may not hold for call {subject}"
        (some s!"may violate `{showComp sub}::{a}`")
        #[s!"counterexample: {showAssignment vals}",
          "help: choose the call's arguments so that the assumption holds, or add an `assume` that guarantees it"]]
    else
    #[one "F0603" s!"expectation {subject} does not hold"
      (some (if r.global then "does not follow from the assumptions and calls" else "does not follow from the guarantees"))
      (#[s!"counterexample: {showAssignment vals}"] ++ priv ++
        #[if r.global then "help: correct the expectation, or assume what it needs"
          else "help: strengthen the guarantees so that it follows, or correct the expectation"])]
  | .fail, .vacuous core =>
    if r.kind == .cover then
      let why := if core.isEmpty then "no behaviour satisfies it" else s!"it is ruled out by {showNames core}"
      #[one "F0615" s!"cover goal {subject} cannot be met: {why}" (some (if r.global then "no values that meet the assumptions and calls satisfy this"
        else "no behaviour that meets the procedure satisfies this"))
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
      (some "not determined") #["note: a `det` variable must have exactly one value for each input",
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

/-- A requirement on an output, phrased as part of a sentence. -/
def forcedRequirement (output : Name) : Forced → String
  | .value value => s!"`{showAnnotationPath output}` to equal {value}"
  | .variant variant => s!"`{showAnnotationPath output}` to match {variant.pattern}"

/-- Supplementary notes express proved relationships under consistent general
premises, never Boolean evaluation at the primary counterexample. -/
def branchMessages (r : CheckResult) : Array Message := Id.run do
  if r.verdict != .fail then return #[]
  let mut out := #[]
  for group in r.branchConflicts do
    let excluded := group.cases.filter (·.excluded)
    if excluded.isEmpty then continue
    let owner := showAnnotationPath group.owner
    let names := (group.premises ++ group.constraints).toList.eraseDups.toArray
    let premise := showNamesAnd names
    let condition := group.condition?.map fun name =>
      if r.kind == .cover then s!"the cover goal `{showAnnotationPath name}`"
      else s!"the condition of `{showAnnotationPath name}`"
    let assumptions := if let some condition := condition then
      if names.isEmpty then condition else premise ++ " and " ++ condition
      else premise
    if group.cases.all (·.excluded) then
      out := out.push {
        severity := .info
        item? := some group.owner
        msg := { code? := none, headline := if assumptions.isEmpty then s!"`{owner}` cannot hold."
          else s!"Assuming {assumptions}, `{owner}` cannot hold." }
      }
    else if !assumptions.isEmpty then
      out := out.push {
        severity := .info
        item? := some group.owner
        msg := { code? := none, headline := s!"The following relationships follow from {assumptions}." }
      }
    for alternative in excluded do
      let name := match alternative.name with
        | .num .. => alternative.name.toString (escape := false)
        | _ => showAnnotationPath alternative.name
      let proposition := match group.kind with
        | .equivalence =>
          let operands := if alternative.label.startsWith "both operands" then "Both operands" else "All operands"
          let value := if alternative.label.endsWith "true" then "true" else "false"
          s!"{operands} of `{owner}` cannot be {value}"
        | .disjunction => s!"`{name}` cannot hold"
        | .exactlyOne => s!"The operands of `{owner}` cannot have only `{name}` true"
      let source := if alternative.text.isEmpty then #[] else #[s!"member: {alternative.text}"]
      let coreNote := if alternative.core.isEmpty then
          "note: No additional constraint is needed to rule this out."
        else s!"note: {showNamesAnd alternative.core}" ++ (if alternative.core.size == 1 then " already rules this out." else " already rule this out.")
      let headline := if alternative.impossible then proposition ++ "."
        else if let some clash := alternative.clashes[0]? then
          let others := if clash.rest.isEmpty then "the stated premises" else showNamesAnd clash.rest
          proposition ++ s!": this would require {forcedRequirement clash.output clash.forced}, while {others}" ++
            (if clash.rest.size == 1 then " requires " else " require ") ++ forcedRequirement clash.output clash.restForced ++ "."
        else proposition ++ "."
      if alternative.opposed.isEmpty || !alternative.clashes.isEmpty then
        out := out.push {
          severity := .info
          item? := some group.owner
          atRange? := alternative.range?
          msg := { code? := none, headline := headline, notes := #[coreNote] ++ source }
        }
      for opposed in alternative.opposed do
        let actual := if opposed.wanted then "false" else "true"
        let reason := if opposed.rest.isEmpty then "the stated premises" else showNamesAnd opposed.rest
        let why := reason ++ (if opposed.rest.size == 1 then " requires " else " require ") ++
          s!"`{showAnnotationPath opposed.member}` to be {actual}."
        out := out.push {
          severity := .info
          item? := some group.owner
          atRange? := opposed.range?
          msg := {
            code? := none
            headline := proposition ++ ": " ++ why
            notes := if opposed.text.isEmpty then #[] else #[s!"member: {opposed.text}"]
          }
        }
  return out

/-- Values and evaluation status of labelled members in a counterexample
or witness, each at its original source range. Passing expectations have
no observations and therefore no failed-member messages. -/
def memberMessages (r : CheckResult) : Array Message := Id.run do
  let mut out := #[]
  for value in r.memberValues do
    let label := match value.evaluated?, value.value? with
      | some false, _ => "not evaluated"
      | some true, some true => "true"
      | some true, some false => "false"
      | _, _ => "unknown"
    out := out.push {
      severity := .info
      item? := some value.owner
      atRange? := value.range?
      msg := {
        code? := none
        headline := s!"`{showAnnotationPath value.name}` is {label}"
        notes := if value.text.isEmpty then #[] else #[s!"member: {value.text}"]
      }
    }
  return out

def messages (hasPrivateOuts : Bool) (r : CheckResult) (decidable : Bool := true) : Array Message :=
  baseMessages hasPrivateOuts r decidable ++ branchMessages r ++ memberMessages r

/-- The help of a warning from testing: from `fren check`, testing a check
set to testing, running `fren check` would not help (`Reqs/Check#checking-by-testing`). -/
def testingHelp (byCheck : Bool) (decide : String) : String :=
  if byCheck then "help: raise `--tests`; the checks set to random testing are not asked of the solver"
  else s!"help: run `fren check` to {decide}, or raise `--tests`"

/-- Testing found no outputs for an admissible input (`eval::test_verdict`). -/
def noOutputsMsg (subject : String) (input : Assignment) (byCheck : Bool := false) : Msg :=
  { code? := some "F0609", headline := s!"testing found no outputs of {subject} for the input {showAssignment input}"
    label? := some "possibly not realizable"
    notes := #["note: the search tries only some values, so outputs may still exist",
      if byCheck then testingHelp true "" else "help: run `fren check` to decide whether it is realizable"] }

/-- No test reached a procedure's checks (`eval::test_verdict`). -/
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

def summary (results : Array CheckResult) (byTesting : Nat := 0) (byBound : Nat := 0) : String :=
  let count (b : Bucket) := (results.filter fun r => bucketOf r.kind r.verdict == b).size
  let parts := (if byTesting == 0 then [] else [s!"{byTesting} by random testing"])
    ++ (if byBound == 0 then [] else [s!"{byBound} by bounded enumeration"])
  let tested := if parts.isEmpty then "" else s!" ({", ".intercalate parts})"
  s!"fren: {count .passed} passed{tested}, {count .failed} failed, {count .inconclusive} inconclusive, \
    {count .redundant} redundant"

end Fren.Core
