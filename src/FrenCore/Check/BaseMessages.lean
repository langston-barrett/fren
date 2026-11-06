-- keep-sorted start
import FrenCore.Check.Decidability
import FrenCore.Check.ReportFormat
-- keep-sorted end

/-!
# Primary check messages

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type} (b : Backend m F V)

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
                   "note: this is a bug in Fren, in reading the solver's model or in translating the spec, or in the solver"] } }]
  | .inconclusive, d =>
    let why := match d with | .unknown w => s!": {w}" | _ => ""
    let what := match r.kind, r.target? with
      | .realizable, some (f, _) => s!"the postconditions of `{showComp f}` can hold"
      | .realizable, _ => s!"{subject} is realizable"
      | .inst, some (sub, a) => match r.subsetTy? with
        | some ty => s!"the parameter `{a.getPrefix}` of `{showComp sub}` has its type `{ty}` for call {subject}"
        | none => s!"the assumption `{a}` of `{showComp sub}` holds for call {subject}"
      | .inst, none => s!"{subject} holds"
      | .expect, _ => s!"{subject} holds"
      | .cover, _ => s!"{subject} can be met"
      | .vacuity, _ => if r.isLawful then s!"the assumptions and calls of {subject} can hold together with its trait's laws"
        else s!"{subject} is vacuous"
      | .redundancy, _ => s!"{subject} is redundant"
      | .determinism, _ => s!"{subject} is determined by the inputs"
      | .definedness, _ => match r.subsetTy? with
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
        #[if r.oneInterpretation then
            s!"note: enumeration searched every behaviour up to size {n}, with each index out of range as `[][0]`, which does not decide it"
          else s!"note: enumeration searched every behaviour up to size {n}, which does not decide it",
          "help: raise `fren.enumeration.size`, or have the solver check it"]
      else if !r.outputQueryInCore then
        #["note: an output type invariant applies an opaque function to a quantified output, so this query is outside the decidable core",
          "help: define the output, or use an output type whose invariants do not apply opaque functions to its value"]
      else match inconclusiveAdvice decidable with
      | .raiseTimeout => #["note: the solver gave up, so this check neither passed nor failed",
        "help: raise the time limit with `--timeout`, or simplify the constraints involved"]
      | .namesConstructs => #["note: the solver gave up, so this check neither passed nor failed",
        "note: the procedure uses constructs outside the decidable core (`undecidable` is allowed), so the solver may never decide it",
        "help: bring it back into the decidable core, or raise the time limit with `--timeout`"]
    -- An expansion of quantifiers over elements that is too large, or
    -- whose model they refute, has a code of its own.
    match d with
    | .undecidedQuantifier n =>
      #[one "F0608" s!"could not decide whether {what}: a quantifier is undecided up to size {n}" (some "undecided")
        #["note: enumeration decides a quantifier by an instance that settles it, a counterexample to a `forall` or a witness of an `exists`, or by every value of its domain, which it could not evaluate here",
          "help: have the solver check it, or raise `fren.enumeration.size` if such an instance is larger"]]
    | .outOfRange =>
      #[one "F0608" s!"could not decide whether {what}: an index out of range may decide it" (some "undecided")
        #["note: enumeration reads every index out of range as `[][0]`, one of the values it may have",
          "help: guard the index, or have the solver check it"]]
    | .unknown w => match unknownReason w with
      | .unsettledPremise =>
        #[one "F0608" s!"could not decide whether {what}" (some "depends on an unproved postcondition")
          #["note: simultaneous induction used all of the function's postconditions",
            "note: another postcondition failed or was inconclusive, so this check cannot be reported as passed",
            "help: establish the other postconditions before relying on this one"]]
      | .recursiveModel =>
        #[one "F0450" s!"could not decide whether {what}" (some "contracts may be too weak")
          #[s!"note: this check fails under the contracts of {((w.drop 21).toString)}",
            "note: evaluation of the recursive definitions does not confirm the counterexample: it refutes it, or cannot evaluate it",
            "help: strengthen those functions' contracts"]]
      | .elements =>
        let (code, notes) := (elementReasonNotes? w).getD ("F0608", advice)
        #[one code s!"could not decide whether {what}{why}" (some "undecided") notes]
      | .refutedModel =>
        #[one "F0608" s!"could not decide whether {what}{why}" (some "undecided")
          #["note: the solver's model was refuted; see the internal error reported for that model"]]
      | .evaluationLimit =>
        #[one "F0608" s!"could not decide whether {what}{why}" (some "evaluation limit")
          #[s!"note: {w}", "help: simplify the expressions involved, or have the solver check it"]]
      | .solver =>
        if decidableUnknown decidable .solver w r.outputQueryInCore r.bounded?.isSome then
          #[{ severity := .error, item? := r.prop?, atIndex? := r.index?, atSite? := r.site?
              msg := { code? := none
                       headline := s!"internal error: the solver did not decide the {kindName r.kind} check of {subject} in the decidable core"
                       label? := some "decidable query was not decided"
                       notes := #[s!"note: the solver's reason was: {w}",
                         "note: no time or resource limit was reached; this is a bug in Fren or the solver"] } }]
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
    let help := if input.all (·.1.isAtomic) then #[s!"help: weaken one of them, or add {aPrecondition false} that rules this input out"]
      else #["help: weaken one of them",
        "note: call variables are part of the system: whatever the calls do, the procedure must cope"]
    #[one "F0601" s!"{subject} is not realizable" (some "not realizable")
      (#[conflictNote "input" input s!"no outputs satisfy {showNamesAnd names}"] ++ help) (item? := none)]
    ++ clashNotes
  | .fail, .counterexample vals =>
    if let (.definedness, some ty) := (r.kind, r.subsetTy?) then
      let m := obligationMsg subject ty (showAssignment vals) priv
      #[one "F0661" m.headline m.label? m.notes]
    else
    if let (.inst, some (sub, a), some ty) := (r.kind, r.target?, r.subsetTy?) then
      let m := instanceTypeMsg subject (showComp sub) (a.getPrefix.toString) ty (showAssignment vals) r.global
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
          s!"help: guard the application, as in `p(x) and f(x) = y`, or add {aPrecondition r.global} that implies the precondition"]]
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
          s!"help: choose the call's arguments so that the assumption holds, or add {aPrecondition r.global} that guarantees it"]]
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

end Fren.Core
