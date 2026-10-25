/-! # What an expression mentions (`Reqs/Lang/Expressions#mentions`)

Whether an expression mentions a variable or an uninterpreted function,
decided over a shape that both front ends translate their syntax into. -/

namespace Fren.Core

/-- The kinds of expression, for whether one mentions a variable or an
uninterpreted function (`lang::mentions`). -/
inductive MentionKind where
  /-- A literal, or a part with no expression, such as a field's name. -/
  | literal
  /-- A constant, a variant without a payload, or another name that is not
  a variable: a path of more than one segment is never one. -/
  | constant
  /-- A variable of the component or of one of its instances, or a field
  read from one. -/
  | variable
  /-- A defined output, whose part is its definition. -/
  | definedOutput
  /-- A binder of a `match` arm, whose part is its scrutinee. -/
  | binder
  /-- A variant with a payload or a record literal, whose parts are its
  arguments or fields. -/
  | construction
  /-- A method call, whose parts are its receiver and arguments. -/
  | method
  /-- An application of an uninterpreted function. -/
  | uninterpreted
  /-- An application of a defined function, whose parts are its arguments. -/
  | defined
  /-- An operator, a conditional, a `match`, a field read or a literal of a
  set, pair or sequence, whose parts are its operands. -/
  | compound
  deriving BEq, Inhabited, Repr

/-- Whether an expression of kind `k` mentions a variable or an
uninterpreted function, where `parts` is whether one of its parts does
(`lang::mentions`). -/
def kindMentions : MentionKind → Bool → Bool
  | .literal | .constant => fun _ => false
  | .variable | .uninterpreted => fun _ => true
  | .definedOutput | .binder | .construction | .method | .defined | .compound => id

/-- An expression as far as what it mentions: its kind and its parts. Both
front ends translate their syntax into it, so that they agree on what an
expression mentions by construction. -/
inductive MentionShape where
  | node (kind : MentionKind) (parts : List MentionShape)
  deriving Inhabited

mutual
/-- Whether `e` mentions a variable or an uninterpreted function
(`lang::mentions`). -/
def MentionShape.mentions : MentionShape → Bool
  | .node k ps => kindMentions k (MentionShape.anyMentions ps)

/-- Whether one of `ps` mentions a variable or an uninterpreted function. -/
def MentionShape.anyMentions : List MentionShape → Bool
  | [] => false
  | p :: ps => p.mentions || MentionShape.anyMentions ps
end

/-- An expression with no parts. -/
def MentionShape.leaf (k : MentionKind) : MentionShape := .node k []

end Fren.Core
