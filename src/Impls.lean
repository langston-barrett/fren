-- Fren's own code, linked to its requirements with `impl`. `lake build`
-- proves each link. It imports every requirement, as `Reqs` does, so that
-- `#fren_trace` sees the components of those that no module implements.
-- keep-sorted start
import Impls.Check
import Impls.Cli
import Impls.Enumeration
import Impls.Eval
import Impls.Fmt
import Impls.Generated
import Impls.Impl
import Impls.Inst
import Impls.Lang
import Impls.Lint
import Impls.Meaning
import Impls.Modules
import Impls.Mutate
import Impls.PatternTypes
import Impls.Refine
import Impls.Trace
import Impls.TypeFacts
import Impls.View
import Reqs
-- keep-sorted end

open Fren.Lang

-- The evidence for each of Fren's components, and the converse of the
-- `tested` claims over the tests. Every requirement must be traced somehow:
-- a component without evidence is a warning, which fails CI's
-- `lake build --wfail`.
set_option fren.requireEvidence "trusted" in
set_option fren.testGlobs "test/**/*.fren src/FrenTest/*.lean src/FrenTestMain.lean" in
#fren_trace
