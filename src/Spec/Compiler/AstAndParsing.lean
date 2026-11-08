import Fren.Impl
import Fren.Literate
import FrenCli.Lex

open Fren.Lang

#fren_md "AstAndParsing.md"

#fren_check

namespace Spec.Compiler.AstAndParsing

/-- Owned rejection fixture for the current checker's real lexer. ASCII makes
its character offsets byte offsets too; this is not a Fren2 parser model. -/
private def slashSource : String := "pub fn quotient(x: Int): Int := x / 2\n"

#guard match FrenCli.lex slashSource.toList.toArray with
  | .error e => e.msg.code? == some "F0105" &&
      e.msg.headline == "`/` is not an operator in Fren" &&
      e.span.start == 34 && e.span.stop == 35 &&
      e.msg.fixes[0]?.map (·.replacement) == some "div"
  | .ok _ => false

/-- Obligation for the eventual shared parser and source emitter, specialized
to a fixed entry category and file identity. This defines a proposition only;
no parser, emitter or proof of this proposition is supplied here. -/
def LosslessOnSuccess {Ast ParseError : Type}
    (parse : String → Except ParseError Ast) (emit : Ast → String) : Prop :=
  ∀ source tree, parse source = .ok tree → emit tree = source

end Spec.Compiler.AstAndParsing
