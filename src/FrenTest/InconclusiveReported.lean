-- keep-sorted start
import FrenCore.Check
-- keep-sorted end

/-! Every inconclusive result is reported (`view::inconclusive_reported`):
`Fren.Core.messages`, which both front ends report, gives an inconclusive
result of every kind, about a constraint or about the whole item, in a
procedure or a global expectation, a warning for each cause of its being
undecided, but for a model that Fren's semantics refutes or a core query
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
  ("binary timeout", .unknown "the solver returned unknown (TIMEOUT)", false),
  ("binary resource limit", .unknown "the solver returned unknown (RESOURCEOUT)", false),
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

-- fren-covers: check::decidable_unknown
#eval show IO Unit from do
  let c : Comp Bool := { path := `query, vars := #[], assumes := #[], reqs := #[], expects := #[], triggers := #[] }
  for reason in ["INCOMPLETE", "", "TIMEOUT", "RESOURCEOUT",
      "the solver returned unknown (TIMEOUT)", "the solver returned unknown (RESOURCEOUT)"] do
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
