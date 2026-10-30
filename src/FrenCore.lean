-- Shared by the Lean-hosted front end and the standalone binary. Depends only
-- on Lean core, and on the binary's parser, with which `FrenCore.Lint` reads
-- the Fren quotations of its fixes (`FrenCli.Quote`).
-- keep-sorted start
import FrenCore.Check
import FrenCore.Closures
import FrenCore.Codes
import FrenCore.Diagnostic
import FrenCore.Evidence
import FrenCore.FnBlocks
import FrenCore.Generics
import FrenCore.Lexical
import FrenCore.Lint
import FrenCore.Literate
import FrenCore.Mentions
import FrenCore.Names
import FrenCore.PatternTypes
import FrenCore.Patterns
import FrenCore.Prelude
import FrenCore.Procedures
import FrenCore.Quantifier
import FrenCore.Recursion
import FrenCore.Regex
import FrenCore.SeqElems
import FrenCore.Sound
import FrenCore.Str
import FrenCore.Syntax
import FrenCore.Table
import FrenCore.Trace
import FrenCore.Ty
-- keep-sorted end
