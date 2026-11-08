import Fren.Impl
import Fren.Literate

open Fren.Lang

#fren_md "AstAndParsing.md"

#fren_check

namespace Spec.Compiler.AstAndParsing

/-- Obligation for the eventual shared parser and source emitter, specialized
to a fixed entry category and file identity. This defines a proposition only;
no parser, emitter or proof of this proposition is supplied here. -/
def LosslessOnSuccess {Ast ParseError : Type}
    (parse : String → Except ParseError Ast) (emit : Ast → String) : Prop :=
  ∀ source tree, parse source = .ok tree → emit tree = source

end Spec.Compiler.AstAndParsing
