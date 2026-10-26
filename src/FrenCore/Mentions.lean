-- keep-sorted start
import FrenCore.Diagnostic
-- keep-sorted end

/-! # What an expression mentions (`Reqs/Lang/Expressions#mentions`)

What an expression mentions: the names of the variables and uninterpreted
functions it may depend on, decided over a shape that both front ends
translate their syntax into. -/

namespace Fren.Core

/-- What an expression mentions (`lang::Mention`): a variable, or an
uninterpreted function, by its name as written, named apart. -/
inductive Mention where
  | var (x : String)
  | fn (f : String)
  deriving BEq, DecidableEq, Inhabited, Repr

/-- `m` as a message writes it. -/
def Mention.describe : Mention → String
  | .var x => s!"the variable `{x}`"
  | .fn f => s!"the function `{f}`"

/-- The kinds of expression, for what one mentions (`lang::mentions`), each
a `lang::Head` (`Reqs/Lang/Meaning#layers`). Only the names that it
mentions are kept: what it mentions does not depend on the rest. -/
inductive MentionKind where
  /-- A literal, or a part with no expression, such as a field's name. -/
  | literal
  /-- A constant, a variant without a payload, or another name that is not
  a variable: a path of more than one segment is never one. -/
  | constant
  /-- A variable `x` of the component or of one of its instances, or a
  field read from one, or the bound name of an unbounded quantifier. -/
  | variable (x : String)
  /-- A defined output, or a name of a `let` or `where`, whose part is its
  definition. -/
  | definition
  /-- A binder of a `match` arm or of a pattern test, whose part is its
  scrutinee. -/
  | binder
  /-- A quantifier's bound name of a listed type: one value in each
  instance. -/
  | bound
  /-- A variant with a payload, a record literal or a newtype built from
  its value, whose parts are its arguments or its fields. -/
  | construction
  /-- A method call, whose parts are its receiver and arguments. -/
  | method
  /-- An application of the uninterpreted function `f`. -/
  | uninterpreted (f : String)
  /-- An application of a defined function, whose parts are its arguments. -/
  | defined
  /-- An operator, a conditional, a `match`, a pattern test, a table, a
  field read, a record update, a `let`, a quantifier or a literal of a set,
  pair or sequence, whose parts are its operands. -/
  | compound
  deriving BEq, Inhabited, Repr

/-- What an expression of kind `k` mentions, where `ps` is what its parts
mention, together (`lang::mentioned_by`). -/
def kindMentioned : MentionKind → List Mention → List Mention
  | .literal | .constant | .bound => fun _ => []
  | .variable x => fun _ => [.var x]
  | .uninterpreted f => fun ps => ps ++ [.fn f]
  | .definition | .binder | .construction | .method | .defined | .compound => id

/-- An expression as far as what it mentions: its kind and its parts. Both
front ends translate their syntax into it, so that they agree on what an
expression mentions by construction. -/
inductive MentionShape where
  | node (kind : MentionKind) (parts : List MentionShape)
  deriving Inhabited

mutual
/-- What `e` mentions, perhaps more than once (`lang::mentions`). -/
def MentionShape.mentioned : MentionShape → List Mention
  | .node k ps => kindMentioned k (MentionShape.allMentioned ps)

/-- What `ps` mention, together. -/
def MentionShape.allMentioned : List MentionShape → List Mention
  | [] => []
  | p :: ps => p.mentioned ++ MentionShape.allMentioned ps
end

/-- Whether `e` mentions a variable or an uninterpreted function
(`lang::mentions`). -/
def MentionShape.mentions (e : MentionShape) : Bool := !e.mentioned.isEmpty

/-- Whether `a * b` is linear, from what each operand mentions
(`lang::linear_product`): one of them mentions nothing. -/
def productAccepted (a b : List Mention) : Bool := a.isEmpty || b.isEmpty

/-- What `ms` mention, each once, as a message lists them. -/
def describeMentions (ms : List Mention) : String :=
  ", ".intercalate (ms.eraseDups.map Mention.describe)

/-- The error of a product of two operands that mention `a` and `b`
(`lang::linear_product`). -/
def nonlinearMsg (a b : List Mention) : Msg :=
  { code? := some "F0307", headline := "nonlinear arithmetic is not supported", label? := some "both sides mention variables or uninterpreted functions"
    notes := #[s!"note: the left side mentions {describeMentions a}, and the right side {describeMentions b}",
      "note: the solver decides only linear integer arithmetic",
      "help: one side of `*` must mention no variable and no uninterpreted function, such as `2 * x` or `(MAX - MIN) * x`"] }

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
