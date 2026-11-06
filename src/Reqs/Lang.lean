-- The chapters share the Fren module `lang`; Lean builds their independent
-- requirements in parallel, while this import preserves the complete API.
-- Keep the manual's order for the shared environment extension.
import Reqs.Lang.Overview
import Reqs.Lang.Lexical
import Reqs.Lang.Types
import Reqs.Lang.SubsetTypes
import Reqs.Lang.BooleanBlocks
import Reqs.Lang.Items
import Reqs.Lang.Generics
import Reqs.Lang.GenericFunctions
import Reqs.Lang.Traits
import Reqs.Lang.Prelude
import Reqs.Lang.Scope
import Reqs.Lang.Procedures
import Reqs.Lang.Global
import Reqs.Lang.Decidability
import Reqs.Lang.Patterns
import Reqs.Lang.Let
import Reqs.Lang.Quantifiers
import Reqs.Lang.ElementQuantifiers
import Reqs.Lang.Semantics
import Reqs.Lang.EvaluationRules
import Reqs.Lang.Expressions
import Reqs.Lang.HigherOrder
import Reqs.Lang.Recursion
import Reqs.Lang.ScopeLaws
import Reqs.Lang.ModulesAndInterfaces
import Reqs.Lang.Implementations
