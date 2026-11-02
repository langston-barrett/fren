-- keep-sorted start
import FrenCore.Check
-- keep-sorted end

/-! Every inconclusive result is reported (`view::inconclusive_reported`):
`Fren.Core.messages`, which both front ends report, gives an inconclusive
result of every kind, about a constraint or about the whole item, in a
procedure or a global expectation, a warning for each cause of its being
undecided, but for a model that Fren's semantics refutes, which has the
internal error instead, and no warning. -/
-- fren-covers: view::inconclusive_reported
open Fren.Core

/-- Each cause of an undecided result, as a `Detail`, and whether it is a
refuted model. -/
private def causes : Array (String × Detail × Bool) := #[
  ("no detail", .none, false),
  ("unknown", .unknown "INCOMPLETE", false),
  ("timeout", .unknown "timeout", false),
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
        for c in causes do
          let (cause, detail, refuted) := c
          let r : CheckResult := { kind, comp := `m.p, prop?, verdict := .inconclusive, detail, global }
          let ms := messages false r
          let warned := ms.any (·.severity matches .warning)
          let errored := ms.any (·.severity matches .error)
          unless warned == !refuted && errored == refuted do
            throw <| IO.userError s!"an inconclusive {repr kind} result ({cause}, prop? {prop?}, global {global}) has warning {warned} and error {errored}"
          n := n + 1
  unless n == CheckKind.all.size * 2 * 2 * causes.size do
    throw <| IO.userError s!"checked {n} results"
