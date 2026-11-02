-- keep-sorted start
import Fren.SimpSet
-- keep-sorted end

/-!
# The last arm of a complete `match`

Where a `match`'s arms are complete, its last arm is taken wherever no
earlier one is, and its Lean definition has no test of its pattern there
(`Fren.Elab`'s `matchTerm`). `lastArm s b` is that arm's body `b`, marked
with the scrutinee `s`: the solver, proofs and enumeration see `b` itself
(`Fren.deltaDefined`), and it prints as `b`, while a model's confirmation, which reads it as an
application, knows its value only where it knows `s`'s, as `lang::eval`'s
`match` and the `fren` command's do (`Reqs/Models#known-values`).
-/

namespace Fren

/-- `b`, the last arm of a complete `match` on `s`. -/
def lastArm.{u, v} {α : Sort u} {β : Sort v} (_s : α) (b : β) : β := b

@[simp, fren_spec] theorem lastArm_eq.{u, v} {α : Sort u} {β : Sort v} (s : α) (b : β) : lastArm s b = b := rfl

/-- A proposition that is a last arm is decided as its body is, as `decide`
proves a generated definition's facts. -/
instance lastArm.decidable {α : Sort u} (s : α) (p : Prop) [h : Decidable p] : Decidable (lastArm s p) := h

/-- A generated definition prints as its user wrote it. -/
@[app_unexpander lastArm] def lastArm.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $_ $b) => `($b)
  | _ => throw ()

end Fren
