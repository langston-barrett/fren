-- keep-sorted start
import FrenCore.Check.Assertions
import FrenCore.Check.Backend
import FrenCore.Check.BaseMessages
import FrenCore.Check.Component
import FrenCore.Check.Conflicts
import FrenCore.Check.Contracts
import FrenCore.Check.Decidability
import FrenCore.Check.Evidence
import FrenCore.Check.Hypotheses
import FrenCore.Check.Model
import FrenCore.Check.Properties
import FrenCore.Check.Query
import FrenCore.Check.Realizability
import FrenCore.Check.ReportFormat
import FrenCore.Check.Reporting
import FrenCore.Check.Run
import FrenCore.Check.Selection
import FrenCore.Check.Sites
import FrenCore.Check.Solver
import FrenCore.Check.Testing
import FrenCore.Check.Types
import FrenCore.Diagnostic
import FrenCore.Names
import FrenCore.Recursion
import FrenCore.SeqElems
import FrenCore.Str
import FrenCore.SubsetTypes
import FrenCore.Table
import FrenCore.Text
import Lean.Data.Name
-- keep-sorted end

/-!
# Checks

The check algorithms and verdicts (`Reqs/Check`), shared by the Lean-hosted
front end and the standalone binary. They are generic over a solver
`Backend`: formulas `F` (Lean terms, or SMT-LIB text) and model values `V`.

Every query asks whether a goal can be proved from hypotheses: `unsat` means
"follows", and `sat` comes with a model.

This compatibility module gathers `FrenCore/Check/*`. Import the parts
a client uses to keep unrelated edits out of its rebuilds. Declaration
names remain in `Fren.Core`; `rg NAME src/FrenCore/Check` finds moved code.
-/
