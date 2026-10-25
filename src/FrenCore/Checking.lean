/-!
# Checking and synthesis (`Reqs/Lang/Types#checking-and-synthesis`)

Whether an expression is checked against a type that where it is written
gives it, or must synthesize its own: `{}` and `[]` can only be checked.
Both front ends decide it with `Position.checked`, from whether the
expression's parts synthesize (`TypeShape.synthesizes`), over a shape that
each builds from its own syntax. Not every site asks: in the Lean-hosted
front end, `toTerm` clears the flag before it elaborates an expression's
parts, so a part that always synthesizes, such as `e is P`'s scrutinee,
an indexed sequence, its index, or a receiver, is passed the flag that
`Position.synthesized` gives without calling it, and a pair's members,
which share the pair's type and give each other nothing, are passed the
pair's own flag, as `Position.shared` gives with no sibling.
-/

namespace Fren.Core

/-- Where an expression is written, for whether it is checked against a
type (`lang::checked`). `declared`: where a type is declared, as a binding,
a field, an argument, a payload, a defined output's definition or a
constant's value. `shared`: a part whose type is the whole's, and every
other such part's: an operand of `union`, `inter`, `minus` or `++`, a
branch of a conditional, the body of a `match` arm, an element of a set or
sequence literal, the expression in parentheses. `compared`: an operand of
`=`, `!=` or `subset`, or the right of `in`, whose type the other operand
gives. `synthesized`: anywhere else. -/
inductive Position where
  | declared | shared | compared | synthesized
  deriving Inhabited, BEq, DecidableEq, Repr

/-- Whether an expression at `p` is checked against a type, from whether the
expression it is a part of is (`expected`), and whether another of the parts
that give it its type synthesizes one (`sibling`) (`lang::checked`). -/
def Position.checked : Position → (expected sibling : Bool) → Bool
  | .declared, _, _ => true
  | .shared, expected, sibling => expected || sibling
  | .compared, _, sibling => sibling
  | .synthesized, _, _ => false

/-- An expression's shape, for whether it synthesizes a type
(`lang::synthesizes`): `{}` or `[]`; one whose type is any of its parts',
the shared ones (see `Position.shared`); a pair, whose type needs both of
its members'; or any other. -/
inductive TypeShape where
  | emptyLiteral
  | anyPart (parts : List TypeShape)
  | pair (a b : TypeShape)
  | other
  deriving Inhabited, Repr

mutual
/-- Whether an expression of shape `s` synthesizes a type (`lang::synthesizes`). -/
def TypeShape.synthesizes : TypeShape → Bool
  | .emptyLiteral => false
  | .anyPart ps => TypeShape.anySynthesizes ps
  | .pair a b => a.synthesizes && b.synthesizes
  | .other => true

/-- Whether one of `ps` synthesizes a type. -/
def TypeShape.anySynthesizes : List TypeShape → Bool
  | [] => false
  | p :: ps => p.synthesizes || TypeShape.anySynthesizes ps
end

end Fren.Core
