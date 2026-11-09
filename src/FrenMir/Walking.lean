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

/-- The full syntax and occurrence contexts are the demand program: if/match
select branches, let binds outcomes, and only and/or may skip their right side.
This asks a downstream consumer to account for demanded definedness. It is
NOT a list of every partial operation asserted without its guards. Consumers
must retain undefined/exhausted/invalid/unsupported outcomes separately from
Boolean results. No analysis or discharge of this request has occurred here. -/
structure Demand where
  root : TypedBody
  deriving Repr, BEq

inductive Question where
  | assumptionsSatisfiable
  | validity (goal : TypedBody)
  deriving Repr, BEq

/-- Assumptions are all and only the written assumptions of one block,
including later ones. No definition is an arbitrary axiom or unproved goal.
Demand roots request source-outcome definedness before Boolean interpretation;
an undefined assumption cannot serve as a false filtering predicate. -/
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
