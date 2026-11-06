-- keep-sorted start
import FrenCore.Diagnostic
import FrenCore.Names
import FrenCore.SeqElems
import FrenCore.Table
import FrenCore.Text
-- keep-sorted end

/-!
# Check results and their details

Part of `FrenCore.Check`, shared by both front ends.
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
  /-- Enumeration found no model, but an index out of range, which it
  reads as `[][0]`, may decide the check in another interpretation
  (`Reqs/Check#searching`). -/
  | outOfRange
  /-- Enumeration found no model, but a quantifier that it did not decide
  up to the bound `n` may decide the check
  (`Reqs/Check#quantifiers-up-to-the-bound`). -/
  | undecidedQuantifier (n : Nat)
  deriving Inhabited

/-- Shared reason for a recursive model that real evaluation does not confirm. -/
def recursiveReason (names : Array Name) : String :=
  "recursive contracts: " ++ ", ".intercalate ((names.toList.eraseDups.mergeSort (fun a b => showPath a < showPath b)).map fun n => s!"`{showPath n}`")

/-- Why the CLI makes a check inconclusive when evaluation refutes its
solver model; the refutation has its own internal error report. -/
def refutedModelReason : String := "the solver's model was refuted"

/-- A refuted model must not be overridden by induction or confused with
an unknown solver answer (`model::report`). -/
def Detail.modelRefuted : Detail → Bool
  | .refuted .. => true
  | .unknown w => w == refutedModelReason
  | _ => false

/-- The origin of an inconclusive reason (`check::unknown_reason`). -/
inductive UnknownReason where
  | solver | unsettledPremise | recursiveModel | elements | refutedModel | evaluationLimit
  deriving BEq, DecidableEq, Repr

/-- An evaluator limit is Fren's reason, not an undecided solver answer. -/
def evaluationDepthReason (depth : Nat) : String := s!"evaluation reached its depth limit of {depth}"

/-- Separate solver answers from the reasons Fren synthesizes after a
query, shared by reporting and realizability's query precedence. -/
def unknownReason (reason : String) : UnknownReason :=
  if reason == "another postcondition used by simultaneous induction did not pass" then .unsettledPremise
  else if Fren.Str.startsWith reason "recursive contracts: " then .recursiveModel
  else if (elementReasonNotes? reason).isSome then .elements
  else if (Detail.unknown reason).modelRefuted then .refutedModel
  else if Fren.Str.startsWith reason "evaluation reached its depth limit of " then .evaluationLimit
  else .solver

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
  /-- For `definedness`, of a value given where a subset type is declared,
  and for `inst`, of an input of a subset type: that type, as written
  (`Reqs/Check#subset-types`). -/
  subsetTy? : Option String := none
  verdict : Verdict
  detail : Detail := .none
  /-- Realizability's generated quantifier stays in the core: no opaque
  application's argument depends on an output it binds
  (`check::output_query_core`). -/
  outputQueryInCore : Bool := true
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
  /-- Decided by an enumeration that read an index out of range, as
  `[][0]`, so that what it searched up to the bound was one interpretation
  of those indexes (`Reqs/Check#searching`). -/
  oneInterpretation : Bool := false
  /-- For `realizable`, of the contract of a generic function without a
  body, checked for every type (`Comp.generic`). -/
  generic : Bool := false
  /-- Of a global expectation with a block, whose messages speak of its
  expectations, assumptions and calls rather than of guarantees; set by the
  front ends where they report it. -/
  global : Bool := false
  /-- The uninterpreted functions with contracts, by their paths, whose
  postconditions the facts of its queries have, as `appFactsWith` finds
  them (`check::CheckRecord`'s `applies`); a check that no query decides
  has none. -/
  applies : Array Name := #[]
  /-- The trait whose laws its queries have among their hypotheses, which
  no check of the item showed can hold (`check::law_premise`). -/
  restsOnLaws? : Option Name := none
  deriving Inhabited

/-- The behaviour that a report shows of the procedure (`view::Shown`): a
counterexample, a witness, or none. -/
inductive Shown where
  | nothing
  | counterexample
  | witness
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The behaviour that the detail `d` shows. Every other detail names
constraints, or says what could not be decided, and shows none. -/
def Detail.shown : Detail → Shown
  | .counterexample _ => .counterexample
  | .witness _ => .witness
  | _ => .nothing

/-- Whether a result of a check of kind `kind` with the verdict `verdict`
may show `shown` (`view::report_shows`): a counterexample only where the
check fails, since it is a behaviour that refutes what the check asks,
and a witness only where a cover goal passes, since it is how the goal is
met. So no report shows a counterexample beside a pass, whatever the
method that reached the verdict. -/
def shownAllowed (kind : CheckKind) (verdict : Verdict) (shown : Shown) : Bool :=
  match shown with
  | .nothing => true
  | .counterexample => verdict == .fail
  | .witness => verdict == .pass && kind == .cover

/-- `r` with its detail dropped where its verdict does not allow the
behaviour it shows (`shownAllowed`). Both front ends seal every result
they report with this, so `shown_sealed` holds of each. -/
def CheckResult.sealShown (r : CheckResult) : CheckResult :=
  if shownAllowed r.kind r.verdict r.detail.shown then r else { r with detail := .none }

theorem shown_sealed (r : CheckResult) :
    shownAllowed r.kind r.verdict r.sealShown.detail.shown := by
  unfold CheckResult.sealShown
  split
  · assumption
  · simp_all [Detail.shown, shownAllowed]

end Fren.Core
