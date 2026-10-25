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
  /-- A variant with a payload, a record literal or a record update, whose
  parts are its arguments, its fields, or its updated value and new
  values. -/
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

/-- The names that a `let` or `where` clause mentions, from those of its
definitions `names`, what each definition mentions (`defs`, as paths whose
first component is the name) and what its body mentions (`body`), with
which definitions are used: mentioned by the body, or by a used later
definition (`Reqs/Lang/Let#meaning`). With `all`, every definition counts,
used or not, as for unused variables and the cycles of defined outputs;
otherwise only the used ones do. A name's mentions in the clause's scope
are its definition's, not mentions of what it shadows. -/
def clauseMentions (names : Array Lean.Name) (defs : Array (Array Lean.Name)) (body : Array Lean.Name) (all : Bool) :
    Array Lean.Name × Array Bool := Id.run do
  let mut acc := body
  let mut used := Array.replicate names.size false
  for k in (List.range names.size).reverse do
    let n := names[k]!
    let mentioned := acc.any (·.getRoot == n)
    if mentioned then used := used.set! k true
    -- Earlier mentions of `n` are of an earlier declaration.
    acc := acc.filter (·.getRoot != n)
    if all || mentioned then acc := acc ++ (defs[k]?.getD #[])
  return (acc, used)

/-- An expression with no parts. -/
def MentionShape.leaf (k : MentionKind) : MentionShape := .node k []

end Fren.Core
