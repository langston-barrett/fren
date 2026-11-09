import Fren.Impl
import Fren.Literate
import Fren.Trace
import FrenParse
import Spec.Language.Syntax

open Fren.Lang

#fren_md "AstAndParsing.md"

#fren_check

namespace Spec.Compiler.AstAndParsing

--@ reference: parsing.lexer.keywords
-- The lexer classifies a word as a keyword exactly when it is in this table.
impl reserved: reserved for (word : String) {
  word := word, keyword? := FrenParse.keywords.contains word
} by
  intro word _
  simp [fren_spec, FrenParse.keywords]

--@ reference: parsing.primitive.space
impl space_case: space_case for (byte : Nat) {
  byte := byte, space? := FrenParse.spaceByte byte
} by
  intro byte _
  simp [fren_spec, FrenParse.spaceByte_iff]; omega

--@ reference: parsing.primitive.continuation
impl continuation_case: continuation_case for (byte : Nat) {
  byte := byte, continuation? := FrenParse.continuationByte byte
} by
  intro byte _
  simp [fren_spec, FrenParse.continuationByte_iff]; omega

--@ reference: parsing.primitive.space
/-- The lexer's whitespace bytes are the ASCII encodings of the lexical
chapter's `WHITESPACE` characters. -/
def space_bytes_agree : Bool :=
  (List.range 256).all fun b =>
    FrenParse.spaceByte b == (b < 128 && decide (String.singleton (Char.ofNat b) ∈ spec.lexical.WHITESPACE))

#guard space_bytes_agree

end Spec.Compiler.AstAndParsing

set_option fren.requireEvidence "trusted" in
#fren_trace
