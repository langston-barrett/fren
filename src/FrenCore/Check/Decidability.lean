-- keep-sorted start
import FrenCore.Check.Types
-- keep-sorted end

/-!
# Decidable solver queries and unknown answers

Part of `FrenCore.Check`, shared by both front ends.
-/

open Lean

namespace Fren.Core

variable {m : Type → Type} [Monad m] {F V : Type}

/-- An unknown solver answer in the decidable core is a bug unless the
query reached a time, resource or memory limit, or was interrupted
(`check::decidable_unknown`).
The two spellings of each limit are the reasons that lean-smt and the
standalone backend give, respectively. This is only for solver answers,
not enumeration, model confirmation or an unsettled premise. -/
def decidableUnknown (procedureCore : Bool) (source : UnknownReason) (reason : String)
    (outputCore : Bool := true) (enumerated : Bool := false) : Bool :=
  procedureCore && outputCore && !enumerated && source == .solver &&
    !(reason == "TIMEOUT" || reason == "RESOURCEOUT" || reason == "MEMOUT" || reason == "INTERRUPTED" ||
      reason == "the solver returned unknown (TIMEOUT)" || reason == "the solver returned unknown (RESOURCEOUT)" ||
      reason == "the solver returned unknown (MEMOUT)" || reason == "the solver returned unknown (INTERRUPTED)")

/-- Whether realizability's generated quantifier is in the core
(`check::output_query_core`). Output type invariants can apply opaque
functions to their value even though an explicit argument cannot mention
an output. Conservatively exclude those applications, including finite
outputs; no exclusion is needed for an output replaced by its definition. -/
def outputQueryInCore (outputs : List String) (applications : List (List String)) : Bool :=
  applications.all fun args => args.all fun name => !outputs.contains name

end Fren.Core
