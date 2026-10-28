-- Fren's own code, linked to its requirements with `impl`. `lake build`
-- proves each link. It imports every requirement, as `Reqs` does, so that
-- `#fren_trace` sees the components of those that no module implements.
-- keep-sorted start
import Impls.Calls
import Impls.Check
import Impls.Cli
import Impls.Elements
import Impls.Enumeration
import Impls.Eval
import Impls.Fmt
import Impls.Generated
import Impls.Global
import Impls.HigherOrder
import Impls.Impl
import Impls.Lang
import Impls.Lint
import Impls.Meaning
import Impls.Modules
import Impls.Mutate
import Impls.PatternTypes
import Impls.Procedures
import Impls.Refine
import Impls.Scope
import Impls.Trace
import Impls.TypeFacts
import Impls.View
import Reqs
-- keep-sorted end

open Fren.Lang

tested lang::global_checks: "test/ui/lang/global.fren", "test/ui/lang/global_preconditions.fren"
tested lang::global_successor: "test/ui/lang/global_preconditions.fren"
tested lang::global_migration_shape: "test/cli/fix/migrate_global_types.fren", "test/cli/fix/migrate_global_empty.fren"
tested lang::global_migration_name: "test/cli/fix/migrate_global.fren", "test/cli/fix/migrate_global_scopes.fren"
tested lang::global_migration_meaning: "src/FrenTestMain.lean"

-- The evidence for each of Fren's components, and the converse of the
-- `tested` claims over the tests. Every requirement must be traced somehow:
-- a component without evidence is a warning, which fails CI's
-- `lake build --wfail`.
set_option fren.requireEvidence "trusted" in
set_option fren.testGlobs "test/**/*.fren src/FrenTest/*.lean src/FrenTestMain.lean" in
#fren_trace
