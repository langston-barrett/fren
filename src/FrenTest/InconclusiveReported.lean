-- keep-sorted start
import FrenCore.Check.Assertions
import FrenCore.Check.Realizability
import FrenCore.Check.Reporting
-- keep-sorted end

/-! Every inconclusive result is reported (`view::inconclusive_reported`):
`Fren.Core.messages`, which both front ends report, gives an inconclusive
result of every kind, about a constraint or about the whole item, in a
procedure or a global expectation, a warning for each cause of its being
undecided, but for a detail carrying a refuted model or a core query
that gives up without reaching a limit, which has the internal error
instead, and no warning. -/
-- fren-covers: view::inconclusive_reported
open Fren.Core

/-- Each cause of an undecided result, as a `Detail`, and whether it has an
internal error in the core. -/
private def causes : Array (String × Detail × Bool) := #[
  ("no detail", .none, false),
  ("unknown", .unknown "INCOMPLETE", true),
  ("empty reason", .unknown "", true),
  ("timeout", .unknown "TIMEOUT", false),
  ("resource limit", .unknown "RESOURCEOUT", false),
  ("memory limit", .unknown "MEMOUT", false),
  ("interrupted", .unknown "INTERRUPTED", false),
  ("evaluation depth", .unknown (evaluationDepthReason 256), false),
  ("binary timeout", .unknown "the solver returned unknown (TIMEOUT)", false),
  ("binary resource limit", .unknown "the solver returned unknown (RESOURCEOUT)", false),
  ("binary memory limit", .unknown "the solver returned unknown (MEMOUT)", false),
  ("binary interrupted", .unknown "the solver returned unknown (INTERRUPTED)", false),
  ("confirmation refuted model", .unknown refutedModelReason, false),
  ("quantifier", .undecidedQuantifier 3, false),
  ("out of range", .outOfRange, false),
  ("induction", .unknown "another postcondition used by simultaneous induction did not pass", false),
  ("recursive contracts", .unknown (recursiveReason #[`m.f]), false),
  ("element limit", .unknown (elementLimitReason 0), false),
  ("elements unconfirmed", .unknown elementUnconfirmedReason, false),
  ("refuted hypothesis", .refuted (.hypothesis `a) #[(`x, "1")], true),
  ("refuted goal", .refuted .goal #[], true)]

#eval show IO Unit from do
  let mut n := 0
  for kind in CheckKind.all do
    for prop? in [(none : Option Lean.Name), some `c] do
      for global in [false, true] do
        for inCore in [false, true] do
          for c in causes do
            let (cause, detail, internal) := c
            let r : CheckResult := { kind, comp := `m.p, prop?, verdict := .inconclusive, detail, global }
            let ms := messages false r inCore
            let internal := internal && (inCore || (detail matches .refuted ..))
            let warned := ms.any (·.severity matches .warning)
            let errored := ms.any (·.severity matches .error)
            unless warned == !internal && errored == internal do
              throw <| IO.userError s!"an inconclusive {repr kind} result ({cause}, prop? {prop?}, global {global}) has warning {warned} and error {errored}"
            n := n + 1
  unless n == CheckKind.all.size * 2 * 2 * 2 * causes.size do
    throw <| IO.userError s!"checked {n} results"

-- A real check's query protocol with a backend that gives up, independent
-- of which queries this version of cvc5 happens to decide.
private def unknownBackend (reason : String) : Backend Id Bool Unit where
  query _ _ _ := pure (.unknown reason)
  falseF := false
  notF := not
  conj := (Array.all · id)
  existsOutputs := pure
  pin _ _ := pure none
  pinVariant _ _ := pure none
  render _ _ := pure ""
  prime := id
  samePrimed _ := true
  subst _ := id

-- fren-covers: check::decidable_unknown, check::unknown_reason
#eval show IO Unit from do
  let c : Comp Bool := { path := `query, vars := #[], assumes := #[], reqs := #[], expects := #[], triggers := #[] }
  for reason in ["INCOMPLETE", "", "TIMEOUT", "RESOURCEOUT", "MEMOUT", "INTERRUPTED", refutedModelReason,
      "the solver returned unknown (TIMEOUT)", "the solver returned unknown (RESOURCEOUT)",
      "the solver returned unknown (MEMOUT)", "the solver returned unknown (INTERRUPTED)"] do
    let r := checkExpect (unknownBackend reason) c (`claim, true)
    let ms := messages false r
    let error := reason == "INCOMPLETE" || reason.isEmpty
    unless r.verdict == .inconclusive && ms.size == 1 &&
        ms[0]!.severity == (if error then .error else .warning) && ms[0]!.item? == some `claim &&
        (if error then ms[0]!.msg.code?.isNone && ms[0]!.msg.headline.startsWith "internal error:"
         else ms[0]!.msg.code? == some "F0608") do
      throw <| IO.userError s!"the query's unknown answer ({reason}) was not reported with its check"
    let bounded := messages false { r with bounded? := some 3 }
    unless bounded.all (·.severity == .warning) do
      throw <| IO.userError "a bounded enumeration result was mistaken for an undecided core query"

-- The shared query classifier receives applications, rather than a front
-- end's precomputed decision. Exercise it through realizability's protocol.
-- fren-covers: check::output_query_core
#eval show IO Unit from do
  let c : Comp Bool := { path := `query, vars := #[{ name := `x, role := .input, isPub := true },
      { name := `y, role := .output, isPub := true }], assumes := #[], reqs := #[], expects := #[], triggers := #[] }
  for apps in [[], [["x"]], [["y"]], [["x"], ["x", "y"]]] do
    let bk := { unknownBackend "INCOMPLETE" with
      query := fun _ _ model => pure (if model then .unknown "INCOMPLETE" else .sat #[])
      outputApplications? := some fun _ => pure apps }
    let r := checkRealizableUniversal bk c
    let core := !(apps.any (·.contains "y"))
    unless r.outputQueryInCore == core && (messages false r).all (·.severity == if core then .error else .warning) do
      throw <| IO.userError s!"incorrect generated output query classification for {apps}"
    let defined := checkRealizableUniversal bk { c with defs := #[(`y, true, true)] }
    unless defined.outputQueryInCore && (messages false defined).all (·.severity == .error) do
      throw <| IO.userError "a substituted output was treated as quantified"
    let assumeUnknown := { bk with query := fun _ _ model => pure (if model then .unsat else .unknown "INCOMPLETE") }
    let assumption := checkRealizableUniversal assumeUnknown c
    unless assumption.outputQueryInCore && (messages false assumption).all (·.severity == .error) do
      throw <| IO.userError "an undecided core assumption query was hidden by the output formula"
    for reason in ["", "INCOMPLETE"] do
      for outputReason in ["TIMEOUT", "INCOMPLETE"] do
        let both := { bk with query := fun _ _ model => pure (.unknown (if model then outputReason else reason)) }
        let r := checkRealizableUniversal both c
        unless r.outputQueryInCore && (match r.detail with | .unknown w => w == reason | _ => false) do
          throw <| IO.userError "the assumptions query's give-up was hidden by the output query"
        unless (messages false r).all (·.severity == .error) do
          throw <| IO.userError "an undecided core assumption query lost its internal error"
    let outputEmpty := { bk with query := fun _ _ model => pure (.unknown (if model then "" else "TIMEOUT")) }
    let empty := checkRealizableUniversal { outputEmpty with outputApplications? := none } c
    unless (match empty.detail with | .unknown w => w.isEmpty | _ => false) && (messages false empty).all (·.severity == .error) do
      throw <| IO.userError "an empty output-query reason was replaced by the assumptions query's timeout"
    for reason in [recursiveReason #[`total], elementUnconfirmedReason, refutedModelReason,
        "another postcondition used by simultaneous induction did not pass"] do
      let synthetic := { bk with
        query := fun _ _ model => pure (.unknown (if model then "INCOMPLETE" else reason))
        outputApplications? := none }
      let r := checkRealizableUniversal synthetic c
      unless (match r.detail with | .unknown w => w == "INCOMPLETE" | _ => false) &&
          (messages false r).all (·.severity == .error) do
        throw <| IO.userError "a non-solver assumption result hid the output query's give-up"
