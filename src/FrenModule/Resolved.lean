module

public import FrenAst
public import FrenBase
public import FrenDiag

public section
namespace FrenModule

inductive ItemKind where
  | enumeration | function | expectation | constructor
  deriving Repr, BEq, DecidableEq

structure Item where
  id : FrenBase.ItemId
  name : FrenAst.Token
  kind : ItemKind
  deriving Repr, BEq

/-- Constructors are stored after their owner, in source order. Keys are
canonical ItemIds, never their potentially colliding display strings. -/
structure Scope where
  id : FrenBase.ItemId
  name : FrenAst.Token
  items : Array Item
  deriving Repr, BEq

abbrev Context := FrenBase.Binding.Context FrenAst.Token

inductive Target where
  | item (id : FrenBase.ItemId)
  | local (index : Nat)
  | boolType | intType
  deriving Repr, BEq, DecidableEq

inductive Role where
  | expression | annotation | pattern
  deriving Repr, BEq, DecidableEq

inductive Written where
  | path (value : FrenAst.Path)
  | builtin (token : FrenAst.Token)
  | implicitBool (parameter : FrenAst.Token)
  deriving Repr, BEq

def Written.anchor : Written → FrenAst.Token
  | .path p => p.head
  | .builtin t | .implicitBool t => t

/-- One entry per semantic occurrence (including implicit parameter types).
Local indices belong to this exact context; sibling index zeroes do not
identify the same binder. Written paths retain every segment's span. -/
structure Reference where
  written : Written
  role : Role
  target : Target
  context : Context
  deriving Repr, BEq

/-- Walking HIR: the lossless structured AST plus all resolved occurrences.
References follow syntax order. Lookup by tape position is unique for accepted
parser documents; implicit types are anchored at their parameter token. No
consumer needs to rerun name lookup to read a target. -/
structure Resolved where
  document : FrenAst.Document
  scope : Scope
  references : Array Reference
  deriving Repr, BEq

def Resolved.referenceAt (result : Resolved) (slice : Nat) : Option Reference :=
  result.references.find? (·.written.anchor.slice == slice)

end FrenModule
