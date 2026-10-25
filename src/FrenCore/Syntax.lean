-- keep-sorted start
import FrenCore.Diagnostic
-- keep-sorted end

/-!
# Messages about syntax

Shared by both front ends where both detect the problem: operators from
other languages, which both parse so as to say what to write instead.
-/

namespace Fren.Core

/-- The Fren operator to write instead of `op`, from another language. -/
def foreignOpFix? : String → Option (String × String)
  | "==" => some ("=", "use `=` to test for equality")
  | "&&" => some ("and", "use `and`")
  | "||" => some ("or", "use `or`")
  | "|" => some ("or", "use `or`")
  | "!" => some ("not ", "use `not` for negation")
  | "/" => some ("div", "use `div`, which divides by a constant")
  | "%" => some ("mod", "use `mod`, the remainder by a constant")
  | _ => none

/-- `op` is an operator of other languages but not Fren's; `spaceBefore`
and `spaceAfter` say whether whitespace surrounds it, so that a word that
replaces it, `div` or `mod`, is kept apart from its operands: `x/2` becomes
`x div 2`. -/
def foreignOpMsg (op : String) (spaceBefore spaceAfter : Bool := true) : Msg :=
  let base : Msg := { code? := some "F0105", headline := s!"`{op}` is not an operator in Fren", label? := some "not a Fren operator" }
  let spaced (r : String) : String :=
    if op == "/" || op == "%" then (if spaceBefore then "" else " ") ++ r ++ (if spaceAfter then "" else " ") else r
  match op, foreignOpFix? op with
  | _, some (r, msg) => { base with fixes := #[{ msg, replacement := spaced r }] }
  | "=>", _ => { base with notes := #["help: write an implication as `when a, b`"] }
  | _, _ => base

end Fren.Core
