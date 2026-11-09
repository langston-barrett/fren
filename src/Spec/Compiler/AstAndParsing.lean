import Fren.Impl
import Fren.Literate
import FrenParse
import Spec.Language.LexicalStructure
import Spec.Language.Syntax
import FrenParseTests

open Fren.Lang

#fren_md "AstAndParsing.md"

#fren_check

namespace Spec.Compiler.AstAndParsing

--@ reference: parsing.primitive.space
/-- `parsing.primitive.space`: the lexer's whitespace bytes are the ASCII
encodings of the lexical chapter's `WHITESPACE` characters. -/
def space_bytes_agree : Bool :=
  (List.range 256).all fun b =>
    FrenParse.spaceByte b == (b < 128 && decide (String.singleton (Char.ofNat b) ∈ spec.lexical.WHITESPACE))

#guard space_bytes_agree

-- Each `tested` or `lean` status of the chapter names a declaration that exists.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let md ← IO.FS.readFile ("src" / "Spec" / "Compiler" / "AstAndParsing.md")
  for name in Spec.Language.LexicalStructure.statusNames md do
    unless (← getEnv).contains name.toName do throwError s!"the status names `{name}`, which does not exist"

end Spec.Compiler.AstAndParsing
