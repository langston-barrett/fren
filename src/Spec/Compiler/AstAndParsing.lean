import Fren.Impl
import Fren.Literate
import FrenParse
import Spec.Language.LexicalStructure

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

end Spec.Compiler.AstAndParsing
