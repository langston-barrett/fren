import Fren.Impl
import Fren.Literate
import FrenCli.Lex
import FrenParse
import Spec.Language.LexicalStructure

open Fren.Lang

#fren_md "AstAndParsing.md"

#fren_check

namespace Spec.Compiler.AstAndParsing

/-- The `fren` command's lexer rejects `/` too, and suggests `div`, as
`lexical.piece.rejected` has it for the parser. ASCII makes its character
offsets byte offsets. -/
private def slashSource : String := "pub fn quotient(x: Int): Int := x / 2\n"

#guard match FrenCli.lex slashSource.toList.toArray with
  | .error e => e.msg.code? == some "F0105" &&
      e.msg.headline == "`/` is not an operator in Fren" &&
      e.span.start == 34 && e.span.stop == 35 &&
      e.msg.fixes[0]?.map (·.replacement) == some "div"
  | .ok _ => false

--@ reference: parsing.primitive.space
/-- `parsing.primitive.space`: the lexer's whitespace bytes are the ASCII
encodings of the lexical chapter's `WHITESPACE` characters. -/
def space_bytes_agree : Bool :=
  (List.range 256).all fun b =>
    FrenParse.spaceByte b == (b < 128 && decide (String.singleton (Char.ofNat b) ∈ spec.lexical.WHITESPACE))

#guard space_bytes_agree

end Spec.Compiler.AstAndParsing
