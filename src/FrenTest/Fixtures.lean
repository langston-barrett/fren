-- keep-sorted start
import FrenCli.Fixture
-- keep-sorted end

/-!
# Fixtures

Fren expressions read by the parser of the `fren` command when this file
is built (`fren_fixture!`), as the trees that the lints read, and the
lints' reports on them.
-/

namespace FrenTest.Fixtures

open FrenCli
open Fren.Core

-- The tree is the binary's: `not` binds more loosely than `=`, and `or`
-- than `and`.
#guard (fren_fixture!{ not a = b }).node.kind == .not
#guard (fren_fixture!{ a? and b? or c? }).node.kind == .bin "or"
-- Its ranges are in the fixture's text.
#guard
  let f := fren_fixture!{ x + (y * 2) }
  f.node.kids.map (textOf f.src ·.range) == #["x", "y * 2"]

-- `nonminimal_bool` on a double negation, through the rules that both
-- front ends call.
#guard
  let f := fren_fixture!{ a? and not not b? }
  ((rewriteReports f.src f.node).map fun (l, _, m) => (l.name, m.fixes.map (·.replacement))) ==
    #[("nonminimal_bool", #["b?"])]

-- `neg_multiply`.
#guard
  let f := fren_fixture!{ x - 1 < -1 * y }
  ((arithReports f.src f.node).map fun r => (r.lint.name, r.msg.fixes.map (·.replacement))) == #[("neg_multiply", #["-y"])]

-- The expression that `Ex.simplerForm` decides on, proved of the tree.
example : (fren_fixture!{ a? and not not b? }).node.toEx 3 = .bin .and (.atom 0) (.not (.not (.atom 0))) := by rfl

end FrenTest.Fixtures
