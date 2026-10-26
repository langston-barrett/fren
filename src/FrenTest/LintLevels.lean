-- keep-sorted start
import Fren.Elab
-- keep-sorted end
open Lean Elab Command

/-- The level of `lint` in effect with the options `set`, as Lean options
set outside the file give them (`lint::outside_options`). -/
def outsideLevelOf (set : List (Name × String)) (lint : Fren.Core.Lint) : CommandElabM Fren.Core.LintLevel := do
  let opts := set.foldl (fun o (n, v) => o.set n v) (← getOptions)
  withScope (fun sc => { sc with opts }) do
    return (← Fren.lintLevel lint).level

-- `forbid` wins, as `-F pedantic -W match_same_arms` keeps
-- `match_same_arms` forbidden on the command line.
/-- info: "forbid" -/
#guard_msgs in
#eval show CommandElabM String from do
  return (← outsideLevelOf [(Fren.Core.Group.pedantic.option, "forbid"),
    (Fren.Core.Lint.matchSameArms.option, "warn")] .matchSameArms).name

/-- info: "forbid" -/
#guard_msgs in
#eval show CommandElabM String from do
  return (← outsideLevelOf [(Fren.Core.Group.pedantic.option, "warn"),
    (Fren.Core.Lint.matchSameArms.option, "forbid")] .matchSameArms).name

-- Otherwise the lint's own option wins over its group's.
/-- info: "allow" -/
#guard_msgs in
#eval show CommandElabM String from do
  return (← outsideLevelOf [(Fren.Core.Group.pedantic.option, "warn"),
    (Fren.Core.Lint.matchSameArms.option, "allow")] .matchSameArms).name

/-- info: "deny" -/
#guard_msgs in
#eval show CommandElabM String from do
  return (← outsideLevelOf [(Fren.Core.Group.pedantic.option, "deny")] .matchSameArms).name
