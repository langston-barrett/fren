-- keep-sorted start
import FrenCli.LintTree
import FrenCli.Quote
import Lean.Elab.Deriving.ToExpr
-- keep-sorted end

/-!
# Fren expressions as test fixtures

`fren_fixture!{ e }` is the Fren expression `e` as the lints read it
(`Fixture`): read by the parser of the `fren` command at Lean's
elaboration time, as `fren_expr!` reads a fix (`FrenCli.Quote`), so that a
unit test or a proof about a concrete example is about what the binary
reads. A quotation that does not parse is an error where it is written.
-/

namespace FrenCli

open Lean Elab Term

/-- A Fren expression: its text, the `fren` command's tree of it, and the
tree that the lints read (`Expr.boolNode`), with its ranges in `text`. -/
structure Fixture where
  text : String
  expr : Expr
  node : Fren.Core.BNode Span
  deriving Inhabited

/-- The text of a fixture, as the lints read it. -/
def Fixture.src (f : Fixture) : Array Char := f.text.toList.toArray

/-- The range of the expression of a fixture, all of its text. -/
def Fixture.range (f : Fixture) : Fren.Core.Range := { start := 0, stop := f.text.length }

-- One type at a time: `deriving instance ToExpr for A, B` derives none for `B`.
deriving instance Lean.ToExpr for FrenCli.Span
deriving instance Lean.ToExpr for FrenCli.Ident
deriving instance Lean.ToExpr for FrenCli.Bound
deriving instance Lean.ToExpr for FrenCli.Pattern
deriving instance Lean.ToExpr for FrenCli.Binder
deriving instance Lean.ToExpr for FrenCli.Expr
deriving instance Lean.ToExpr for Fren.Core.BKind
deriving instance Lean.ToExpr for Fren.Core.Range

/-- `n` as a Lean term. -/
partial def bnodeToExpr : Fren.Core.BNode Span → MetaM Lean.Expr
  | .mk k r a kids => do
    let kids ← Meta.mkArrayLit (mkApp (mkConst ``Fren.Core.BNode) (mkConst ``Span)) (← kids.toList.mapM bnodeToExpr)
    return mkAppN (mkConst ``Fren.Core.BNode.mk) #[mkConst ``Span, toExpr k, toExpr r, toExpr a, kids]

/-- `fren_fixture!{ e }`: the Fren expression `e` as the lints read it
(`FrenCli.Fixture`). -/
syntax (name := frenFixture) "fren_fixture!{" Quote.body "}" : term

@[term_elab frenFixture] def elabFrenFixture : TermElab := fun stx _ => do
  let parts := stx[1].getArgs
  unless parts.all (·.isAtom) do throwErrorAt stx[1] "a fixture has no antiquotations"
  let text := (String.join (parts.toList.map (·.getAtomVal))).trimAsciiEnd.toString
  let (e, src) ← match Quote.parseExpr text with
    | .ok r => pure r
    | .error msg => throwErrorAt stx[1] "in the Fren fixture `{text}`: {msg}"
  let node ← bnodeToExpr (e.boolNode src)
  return mkAppN (mkConst ``Fixture.mk) #[toExpr text, toExpr e, node]

end FrenCli
