-- keep-sorted start
import FrenCore.Check.BaseMessages
-- keep-sorted end

/-!
# Supplementary check messages

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type} (b : Backend m F V)

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
  -- The members' values are of the model, so a model that Fren's semantics
  -- contradicts, and that is therefore not shown, shows none of them
  -- either (`Reqs/Models#reporting`).
  if r.detail matches .refuted .. then return out
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

/-- A constraint whose verdict rests on the laws of the trait `t`, whose
consistency is not checked (`F0665`, `check::law_premise`): laws that
contradict each other would give that verdict whatever the constraint
says. -/
def lawsMsg (what : String) (t : Name) : Msg :=
    { code? := some "F0665"
      headline := s!"{what} rests on the laws of `{showComp t}`, whose consistency is not checked"
      label? := some "rests on unchecked laws"
      notes := #[s!"note: its verdict comes from the laws of `{showComp t}`; if no interpretation meets them all, it would be the same whatever it says",
        "note: Fren does not check yet that a trait's laws can hold together (#594)"] }

/-- The message of a result that rests on a trait's laws (`lawsMsg`), at
its constraint, or none. -/
def lawsMessages (r : CheckResult) : Array Message :=
  match r.restsOnLaws? with
  | some t =>
    let subject := match r.prop? with
      | some n => s!"`{showComp (r.comp ++ n)}`"
      | none => s!"`{showComp r.comp}`"
    #[{ severity := .warning, item? := r.prop?, atIndex? := r.index?, atSite? := r.site?, msg := lawsMsg subject t }]
  | none => #[]

/-- The messages of one result, which both front ends report. The result
shows a behaviour only where its verdict allows it: it is sealed here, so
that no message of a pass shows a counterexample, whatever method reached
the verdict (`view::report_shows`). -/
def messages (hasPrivateOuts : Bool) (r : CheckResult) (decidable : Bool := true) : Array Message :=
  let r := r.sealShown
  baseMessages hasPrivateOuts r decidable ++ branchMessages r ++ memberMessages r ++ lawsMessages r

/-- Sealing twice is sealing once. -/
theorem CheckResult.sealShown_idem (r : CheckResult) : r.sealShown.sealShown = r.sealShown := by
  unfold CheckResult.sealShown
  split
  · simp_all
  · simp [Detail.shown, shownAllowed]

/-- The messages of a result are those of its sealed result, which shows
only what its verdict allows (`shown_sealed`): whatever a producer put in
it, no report shows a counterexample beside a pass (`view::report_shows`).
Without the seal in `messages`, this would not hold. -/
theorem messages_sealed (h : Bool) (r : CheckResult) (d : Bool) :
    messages h r d = messages h r.sealShown d := by
  simp only [messages, CheckResult.sealShown_idem]

end Fren.Core
