-- keep-sorted start
import FrenCore.Ty
-- keep-sorted end

/-!
# Checking and synthesis (`Reqs/Lang/Types#checking-and-synthesis`)

Whether an expression is checked against a type that where it is written
gives it, or must synthesize its own: `{}` and `[]` can only be checked.
Each front end classifies the place where it elaborates an expression as
an `ExprSite`, and both decide from `ExprSite.position` whether it is checked
(`ExprSite.checked`), from whether the expression's parts synthesize
(`TypeShape.synthesizes`), over a shape that each builds from its own
syntax, and against which type (`ExprSite.expected`). Not every site asks: in
the Lean-hosted front end, `toTerm` clears the flag before it elaborates
an expression's parts, so a part that always synthesizes, such as an
operand of arithmetic, an indexed sequence, its index, or a receiver, is
passed the flag that `Position.synthesized` gives without calling it; and
the `fren` command expects no type of an expression unless its site gives
one.
-/

namespace Fren.Core

/-- The kind of place an expression is written in, for whether it is
checked against a type (`lang::checked`), which `ExprSite.position` gives for
each site. `declared`: where a type is declared; `shared`: a part whose
type is the whole's, and every other such part's; `compared`: an operand
whose type the other operand gives; `synthesized`: anywhere else. -/
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

/-- A place where an expression is written, as both front ends classify
their syntax (`lang::checked`). -/
inductive ExprSite where
  /-- A binding `x := e` of a call, or an argument of a refinement. -/
  | binding
  /-- A field of a record literal or of a record update. -/
  | recordField
  /-- The value of a newtype, as `e` in `Ms(e)`. -/
  | newtypeValue
  /-- An argument of a function application. -/
  | functionArgument
  /-- A value of a variant's payload. -/
  | payload
  /-- An argument of a sequence's method, typed by its parameter. -/
  | seqMethodArgument
  /-- The argument of an enumeration's or record's `min` or `max`, against
  the receiver's type. -/
  | orderedMethodArgument
  /-- A defined output's definition, as a function block's `out`. -/
  | outputDefinition
  /-- A defined function's body, against its result type. -/
  | functionBody
  /-- A constant's value. -/
  | constantValue
  /-- A definition of a `let` or `where` whose type is written. -/
  | typedDefinition
  /-- The body of a closure whose result type is known. -/
  | typedClosureBody
  /-- An operand of `union`, `inter` or `minus`. -/
  | setOperand
  /-- An operand of `++`. -/
  | concatOperand
  /-- A branch of a conditional. -/
  | branch
  /-- The body of a `match` arm. -/
  | armBody
  /-- The value of a table's row. -/
  | rowValue
  /-- An element of a set or sequence literal. -/
  | element
  /-- The expression in parentheses. -/
  | parenthesized
  /-- The body of a `let`. -/
  | letBody
  /-- A member of a pair, which gives the other nothing. -/
  | pairMember
  /-- An operand of `=`, `!=` or an ordering. -/
  | comparedOperand
  /-- An operand of `subset`. -/
  | subsetOperand
  /-- The right of `in`. -/
  | membershipRight
  /-- The left of `in`. -/
  | membershipLeft
  /-- An operand of `join`. -/
  | joinOperand
  /-- The right of `++` on strings, which is a `String`. -/
  | stringOperand
  /-- An argument of a method of anything but a sequence, an enumeration or
  a record. -/
  | methodArgument
  /-- The receiver of a method or of a field read. -/
  | receiver
  /-- The scrutinee of a `match` or of `e is P`. -/
  | scrutinee
  /-- The guard of a `match` arm. -/
  | armGuard
  /-- The condition of a table's row. -/
  | rowCondition
  /-- The updated value of a record update. -/
  | updatedRecord
  /-- A definition of a `let` or `where` whose type is not written. -/
  | untypedDefinition
  /-- The body of a closure whose result type is not known. -/
  | untypedClosureBody
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The position of an expression written at `s` (`lang::checked`). -/
def ExprSite.position : ExprSite → Position
  | .binding | .recordField | .newtypeValue | .functionArgument | .payload
  | .seqMethodArgument | .orderedMethodArgument | .outputDefinition | .functionBody | .constantValue
  | .typedDefinition | .typedClosureBody => .declared
  | .setOperand | .concatOperand | .branch | .armBody | .rowValue | .element | .parenthesized
  | .letBody | .pairMember => .shared
  | .comparedOperand | .subsetOperand | .membershipRight => .compared
  | .membershipLeft | .joinOperand | .stringOperand | .methodArgument | .receiver | .scrutinee | .armGuard
  | .rowCondition | .updatedRecord | .untypedDefinition | .untypedClosureBody => .synthesized

/-- Whether an expression at `s` is checked against a type, from whether the
expression it is a part of is (`expected`), and whether another of the parts
that give it its type synthesizes one (`sibling`) (`lang::checked`). -/
def ExprSite.checked (s : ExprSite) (expected sibling : Bool) : Bool := s.position.checked expected sibling

/-- The type expected of an expression at `p`, from the type `whole`
declared or expected of the whole, and the type `sibling` of a part that
shares its type or is compared with it, if that one synthesizes it
(`lang::expected_type`): the declared type; for a shared part, the
sibling's, widened, unless a `Nat` is expected of the whole, and otherwise
the whole's; for a compared one, the other operand's; and none for a
synthesized one. It is given exactly where `Position.checked` holds
(`expected_isSome`). The bodies of a `match`'s arms and the values of a
table's rows take the whole's type first: their callers pass the arms or
rows before them as `sibling` only where no type is expected of the whole
(a checklist item of #545 is whether the other shared parts should too). -/
def Position.expected : Position → (whole sibling : Option Ty) → Option Ty
  | .declared, whole, _ => whole
  | .shared, whole, sibling => if whole == some .nat then whole else (sibling.map Ty.widen).orElse fun _ => whole
  | .compared, _, sibling => sibling
  | .synthesized, _, _ => none

/-- The type expected of an expression at `s` (`Position.expected`). -/
def ExprSite.expected (s : ExprSite) (whole sibling : Option Ty) : Option Ty := s.position.expected whole sibling

/-- A type is expected of an expression exactly where it is checked, given
a declared type where one is declared. -/
theorem Position.expected_isSome (p : Position) (whole sibling : Option Ty) (h : p = .declared → whole.isSome) :
    (p.expected whole sibling).isSome = p.checked whole.isSome sibling.isSome := by
  cases p <;> cases whole <;> cases sibling <;> simp_all [Position.expected, Position.checked] <;> split <;> simp_all

/-- An expression's shape, for whether it synthesizes a type
(`lang::synthesizes`): `{}` or `[]`; one whose type is any of its parts',
the shared ones (see `Position.shared`); a pair, whose type needs both of
its members'; a variant or record of a generic type, whose type needs an
argument for each of its type parameters, from any of the values of its
payload or fields whose declared types mention it; or any other. -/
inductive TypeShape where
  | emptyLiteral
  | anyPart (parts : List TypeShape)
  | pair (a b : TypeShape)
  /-- For each type parameter, the shapes of the values whose declared
  types mention it (`Reqs/Lang/Generics#type-arguments`). -/
  | construction (params : List (List TypeShape))
  | other
  deriving Inhabited, Repr

mutual
/-- Whether an expression of shape `s` synthesizes a type (`lang::synthesizes`). -/
def TypeShape.synthesizes : TypeShape → Bool
  | .emptyLiteral => false
  | .anyPart ps => TypeShape.anySynthesizes ps
  | .pair a b => a.synthesizes && b.synthesizes
  | .construction ps => TypeShape.allGiven ps
  | .other => true

/-- Whether one of `ps` synthesizes a type. -/
def TypeShape.anySynthesizes : List TypeShape → Bool
  | [] => false
  | p :: ps => p.synthesizes || TypeShape.anySynthesizes ps

/-- Whether each type parameter, given the shapes of the values whose
declared types mention it, is given an argument: one of them synthesizes
its type. -/
def TypeShape.allGiven : List (List TypeShape) → Bool
  | [] => true
  | p :: ps => TypeShape.anySynthesizes p && TypeShape.allGiven ps
end

/-- How an expression is written, for whether the right of `in` is checked
against a sequence (`lang::written_sequence`): a sequence literal; one
whose type is that of its shared parts, as a `++`, a conditional, a
`match`, a table, a `let` or parentheses; or any other. -/
inductive WrittenShape where
  | seqLiteral
  | sharedParts (parts : List WrittenShape)
  | other
  deriving Inhabited, Repr

mutual
/-- Whether an expression of shape `s` is written as a sequence: it is a
sequence literal, or one of its shared parts is written as one
(`lang::written_sequence`). -/
def WrittenShape.sequence : WrittenShape → Bool
  | .seqLiteral => true
  | .sharedParts ps => WrittenShape.anySequence ps
  | .other => false

/-- Whether one of `ps` is written as a sequence. -/
def WrittenShape.anySequence : List WrittenShape → Bool
  | [] => false
  | p :: ps => p.sequence || WrittenShape.anySequence ps
end

end Fren.Core
