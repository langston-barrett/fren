-- keep-sorted start
import Fren.Check
-- keep-sorted end

/-! The Lean-hosted front end's script of a query, for the obligations dump
(`Fren.queryShown`): what lean-smt showed after `query:`, even if it threw
after showing it; the error, if it threw before; and otherwise an
`(error ...)` that says that it showed none, never an empty script, which
the dump would print as an obligation with an empty context
(`Reqs/Cli#obligations`). -/

namespace FrenTest.QueryShown

open Lean Meta

/-- The script that `queryShown` gives for `act`. -/
private def scriptOf (act : MetaM Unit) : MetaM String := return (← Fren.queryShown act).2

#eval show MetaM Unit from do
  unless (← scriptOf (pure ())) == Fren.Core.errorScript Fren.noQueryShown do
    throwError "a query that lean-smt did not show must be an (error ...) script"
  unless (← scriptOf (logInfo "goal: False\n\nquery:\n(assert x)")) == "(assert x)" do
    throwError "the query that lean-smt showed must be the script"
  unless (← scriptOf (do logInfo "goal: g\n\nquery:\n(assert y)"; throwError "late")) == "(assert y)" do
    throwError "a query shown before a throw must be the script"
  unless (← scriptOf (throwError "early")) == Fren.Core.errorScript "early" do
    throwError "a throw before any query must be its (error ...) script"

end FrenTest.QueryShown
