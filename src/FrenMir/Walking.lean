module

public import FrenModule.Typed

public section
namespace FrenMir
open FrenModule

/-- A deliberately small walking theory. Its expressions are the retained
actual typed bodies, not another syntax tree or a lowered logical language. -/
structure Enumeration where
  id : FrenBase.ItemId
  written : FrenAst.Decl
  constructors : Array (FrenBase.ItemId × FrenAst.Token)
  deriving Repr, BEq

structure Function where
  signature : Signature
  definition : TypedBody
  deriving Repr, BEq

/-- Exists even for an empty block. Parameters are in written order; context
is nearest first. Members include their full written role, label and tokens. -/
structure Block where
  owner : FrenBase.ItemId
  written : FrenAst.Decl
  parameters : Array TypedParameter
  context : TypeContext
  members : Array TypedBody
  deriving Repr, BEq

inductive Declaration where
  | enumeration (value : Enumeration)
  | function (value : Function)
  | block (value : Block)
  deriving Repr, BEq

/-- Full syntax and lexical occurrences are retained static verification roots.
Both Boolean operands and unused definitions contribute obligations in their
incoming contexts; explicit if/match branches supply conditional contexts.
Consumers retain scopes and origins until condition generation. Raw
undefined/exhausted/invalid/unsupported outcomes stay separate from Boolean
values and do not select obligations. No discharge has occurred here. -/
structure Demand where
  root : TypedBody
  deriving Repr, BEq

inductive Question where
  | assumptionsSatisfiable
  | validity (goal : TypedBody)
  deriving Repr, BEq

/-- Assumptions are all and only the written assumptions of one block,
including later ones. No definition is an arbitrary axiom or unproved goal.
Static roots request declarative source well-definedness, independently of
raw evaluation traces; an undefined assumption is not a false predicate. -/
structure CheckRequest where
  owner : FrenBase.ItemId
  parameters : Array TypedParameter
  context : TypeContext
  assumptions : Array TypedBody
  question : Question
  demand : Array Demand
  deriving Repr, BEq

structure Theory where
  source : Typed
  declarations : Array Declaration
  requests : Array CheckRequest
  deriving Repr, BEq

/-- Selection is by written member kind, never by position or proved status. -/
@[expose] def Block.assumptions (b : Block) : Array TypedBody :=
  b.members.filter fun m => m.member.any (·.kind == .assume)

@[expose] def Block.goals (b : Block) : Array TypedBody :=
  b.members.filter fun m => m.member.any (·.kind == .expect)

/-- One satisfiability request even with no assumptions or no members; each
written goal then gets a distinct validity request. Definitions live in Theory.
The demand programs remain structured, including all lexical occurrences. -/
@[expose] def Block.requests (b : Block) : Array CheckRequest :=
  let assumptions := b.assumptions
  let demand := assumptions.map Demand.mk
  #[⟨b.owner, b.parameters, b.context, assumptions, .assumptionsSatisfiable, demand⟩] ++
    b.goals.map fun goal =>
      ⟨b.owner, b.parameters, b.context, assumptions, .validity goal, demand.push ⟨goal⟩⟩

end FrenMir
