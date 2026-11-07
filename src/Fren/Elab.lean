-- keep-sorted start
import Fren.Elab.AbstractTypes
import Fren.Elab.Applications
import Fren.Elab.Arithmetic
import Fren.Elab.Blocks
import Fren.Elab.Closures
import Fren.Elab.ComparisonLints
import Fren.Elab.Comparisons
import Fren.Elab.Constants
import Fren.Elab.Construction
import Fren.Elab.Context
import Fren.Elab.Contracts
import Fren.Elab.DataTypes
import Fren.Elab.Declarations
import Fren.Elab.Definitions
import Fren.Elab.Evidence
import Fren.Elab.ExpressionLints
import Fren.Elab.FunctionSupport
import Fren.Elab.Functions
import Fren.Elab.GlobalBlocks
import Fren.Elab.GlobalExpectations
import Fren.Elab.Guards
import Fren.Elab.Induction
import Fren.Elab.Instances
import Fren.Elab.Matches
import Fren.Elab.MemberLints
import Fren.Elab.Mentions
import Fren.Elab.MutualFunctions
import Fren.Elab.Names
import Fren.Elab.Paths
import Fren.Elab.PatternLints
import Fren.Elab.Patterns
import Fren.Elab.Predicates
import Fren.Elab.ProcedureParts
import Fren.Elab.ProcedureSyntax
import Fren.Elab.Procedures
import Fren.Elab.Quantifiers
import Fren.Elab.Records
import Fren.Elab.Sequences
import Fren.Elab.Sets
import Fren.Elab.SubsetDeclarations
import Fren.Elab.SubsetTypes
import Fren.Elab.Syntax
import Fren.Elab.Tables
import Fren.Elab.Terms
import Fren.Elab.Traits
import Fren.Elab.TypeTerms
import Fren.Elab.Types
-- keep-sorted end

/-!
# Elaborators

These are the only code that changes the Fren model. Each records Fren's own
representation of a declaration, then generates ordinary Lean declarations
from it (an `inductive` per enum; a `def` per constant; a `def` per
`assume`/`ensure`/`expect`, plus `assumes` and `ensures`, per procedure; a `def` per
global expectation) so that specs can be used from Lean.

This compatibility module gathers `Fren/Elab/*`. Import the parts a client
uses to keep unrelated edits out of its rebuilds. Declaration names remain
in `Fren`; `rg NAME src/Fren/Elab` finds moved code.
-/
