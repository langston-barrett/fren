/-!
# Guards (`Reqs/Lang/Expressions#sequences`)

The operands that are evaluated only under a condition, and the guard that
each adds: an index in one need only be in range when its guard holds
(`check::definedness`). Both front ends build their guards with
`GuardedOperand.guard`, over their own representation of a condition.
-/

namespace Fren.Core

/-- An operand that is evaluated only under a condition (`lang::guard`): the
body of `when` and of `unless`, the branches of a conditional, the right
operand of `and` and of `or`, and the guard and the body of a `match` arm. -/
inductive GuardedOperand where
  | whenBody | unlessBody | thenBranch | elseBranch | andRight | orRight | armGuard | armBody
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether `o` is evaluated when its condition holds, rather than when it
fails (`lang::guard`). Its condition is that of `when`, `unless` or the
conditional, the left operand of `and` or `or`, for an arm's guard, that its
pattern matches and no earlier arm is taken, and for its body, that the arm
is the first that is taken. -/
def GuardedOperand.whenHolds : GuardedOperand → Bool
  | .whenBody | .thenBranch | .andRight | .armGuard | .armBody => true
  | .unlessBody | .elseBranch | .orRight => false

/-- The guard of `o`, from its condition `c` and its negation `notC`. -/
def GuardedOperand.guard (o : GuardedOperand) (c notC : α) : α := if o.whenHolds then c else notC

end Fren.Core
