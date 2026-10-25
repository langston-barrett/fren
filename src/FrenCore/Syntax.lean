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

/-- `<-`, which Lean lexes as one token, so that `x <- 1` is not `x < -1`
(`Reqs/Lang/Lexical#punctuators`). -/
def leftArrowMsg : Msg :=
  { code? := some "F0121", headline := "`<-` is not an operator in Fren", label? := some "one token, as in Lean"
    notes := #["note: Lean lexes `<-` as one token, so Fren does too: `x <- 1` is not `x < -1`"]
    fixes := #[{ msg := "write `< -` to compare with a negation", replacement := "< -" }] }

/-! ## Chained comparisons -/

/-- The kind of an operator of a comparison, for chaining
(`lang::comparison_chain`). -/
inductive ChainKind where
  /-- `<` and `<=`. -/
  | ascending
  /-- `>` and `>=`. -/
  | descending
  /-- `=`, `!=`, `in`, `subset` and `is`. -/
  | other
  deriving Inhabited, BEq, DecidableEq, Repr

def ChainKind.ofOp : String → ChainKind
  | "<" | "<=" => .ascending
  | ">" | ">=" => .descending
  | _ => .other

/-- Whether a comparison with these numbers of operators of each kind is
accepted (`lang::comparison_chain`). -/
def chainAccepted (ascending descending other : Nat) : Bool :=
  ascending + descending + other == 1 || (other == 0 && (ascending == 0 || descending == 0))

/-- `op`, which does not chain, in a chained comparison. -/
def chainOtherMsg (op : String) : Msg :=
  { code? := some "F0108", headline := s!"`{op}` cannot be chained", label? := some "cannot be chained"
    notes := #["note: only `<` and `<=` chain together, and `>` and `>=`",
      -- `a in b and b in c` would compare `b` with a member and a set, and
      -- `is` has a pattern on its right.
      if op == "in" || op == "is" then "help: split the chain with `and`, or put a comparison in parentheses to compare its result"
      else s!"help: split the chain with `and`, e.g. `a {op} b and b {op} c`, or put a comparison in parentheses to compare its result"] }

/-- `second`, which orders the other way from `first`, in a chained
comparison. -/
def chainDirectionMsg (first second : String) : Msg :=
  { code? := some "F0122", headline := s!"`{first}` and `{second}` cannot be chained together"
    label? := some s!"orders the other way from `{first}`"
    notes := #["note: a chained comparison orders one way: `<` and `<=` chain together, and `>` and `>=`",
      "help: split the chain with `and`, e.g. `a < b and b > c`"] }

/-- Checks the operators of a chained comparison
(`lang::comparison_chain`): if it is rejected, the index of the operator
to report and the message. That is the first that does not chain, else
the first that orders the other way from the first. -/
def checkChain (ops : Array String) : Except (Nat × Msg) Unit :=
  let kinds := ops.map ChainKind.ofOp
  let count (k : ChainKind) := (kinds.filter (· == k)).size
  if chainAccepted (count .ascending) (count .descending) (count .other) then .ok () else
  match kinds.findIdx? (· == .other) with
  | some i => .error (i, chainOtherMsg ops[i]!)
  | none =>
    let i := (kinds.findIdx? (· != kinds[0]!)).getD 0
    .error (i, chainDirectionMsg ops[0]! ops[i]!)

end Fren.Core
