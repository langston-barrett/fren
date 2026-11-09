module

public import FrenMir

public section
namespace FrenLir
open FrenModule FrenAst

/-- Both symbols of a definition take ordinary positional values. Domain is
declarative well-definedness of its written body, never a solver success
or fuel predicate. -/
inductive Component where
  | value | domain
  deriving Repr, BEq, DecidableEq

structure Origin where
  owner : FrenBase.ItemId
  member : Option Member
  expression : Expr
  context : TypeContext
  deriving Repr, BEq

/-- A first-order vocabulary with scoped outcome lets. There is deliberately
no global ref table: all open expressions stay under their lexical binders.
Arithmetic values are total symbolic terms; verification retains div/mod checks.
An at node preserves each written occurrence, including parentheses. -/
inductive Term where
  | bool (value : Bool)
  | int (value : Int)
  | constructor (owner id : FrenBase.ItemId)
  | local (type : FrenExpr.Ty) (slot : Nat) (component : Component)
  | unary (op : UnaryOp) (operand : Term)
  | binary (op : BinaryOp) (left right : Term)
  | ite (condition yes no : Term)
  | app (signature : Signature) (component : Component) (arguments : List Term)
  | letE (binder : Token) (type : FrenExpr.Ty) (value domain body : Term)
  | at (origin : Origin) (term : Term)
  deriving Repr, BEq

/-- Scoped verification information, retained until LIR -> OIR. A check is a
proof obligation, not an asserted hypothesis or a discharged condition. Both
written Boolean operands and unused let definitions contribute checks. Only
explicit branches introduce guards. No assert/subset syntax is admitted here. -/
inductive Verification where
  | empty
  | check (condition : Term)
  | both (left right : Verification)
  | branch (condition : Term) (yes no : Verification)
  | letE (binder : Token) (type : FrenExpr.Ty) (value domain : Term) (body : Verification)
  | at (origin : Origin) (body : Verification)
  deriving Repr, BEq

@[expose] def both (a b : Term) : Term := .binary .and a b

/-- A summary of retained obligations, not OIR condition generation. Scoped
checks remain available individually with their original guards and binders.
Partial-operation values outside this domain remain unspecified. -/
@[expose] def Verification.formula : Verification → Term
  | .empty => .bool true
  | .check condition => condition
  | .both a b => FrenLir.both a.formula b.formula
  | .branch c a b => .ite c a.formula b.formula
  | .letE binder ty v d body => .letE binder ty v d body.formula
  | .at origin body => .at origin body.formula

structure Lowered where
  value : Term
  verification : Verification
  deriving Repr, BEq

@[expose] def Lowered.defined (v : Lowered) : Term := v.verification.formula

/-- Declarative source verification does not consult a concrete evaluation
trace or Boolean value to decide whether an ordinary operand is checked. -/
@[expose] def Lowered.binary (op : BinaryOp) (a b : Lowered) : Lowered :=
  let operands := Verification.both a.verification b.verification
  let checks := match op with
    | .div | .mod => Verification.both operands (.check (.binary .ne b.value (.int 0)))
    | _ => operands
  ⟨.binary op a.value b.value, checks⟩

@[expose] def Lowered.branch (c yes no : Lowered) : Lowered :=
  ⟨.ite c.value yes.value no.value,
    .both c.verification (.branch c.value yes.verification no.verification)⟩

@[expose] def Lowered.bind (binder : Token) (type : FrenExpr.Ty) (v body : Lowered) : Lowered :=
  ⟨.letE binder type v.value v.defined body.value,
    .both v.verification (.letE binder type v.value v.defined body.verification)⟩

@[expose] def Lowered.call (sig : Signature) (args : List Lowered) : Lowered :=
  let values := args.map (·.value)
  ⟨.app sig .value values,
    .both (args.foldr (fun a rest => .both a.verification rest) .empty)
      (.check (.app sig .domain values))⟩

@[expose] def Lowered.mark (origin : Origin) (v : Lowered) : Lowered :=
  ⟨.at origin v.value, .at origin v.verification⟩

structure Body where
  source : TypedBody
  term : Lowered
  deriving Repr, BEq

inductive Declaration where
  | enumeration (value : FrenMir.Enumeration)
  | function (signature : Signature) (definition : Body)
  | block (source : FrenMir.Block) (members : Array Body)
  deriving Repr, BEq

inductive Question where
  | assumptionsSatisfiable
  | validity (goal : Body)
  deriving Repr, BEq

/-- No query is asserted or discharged here. Verification roots stay separate
from Boolean assumptions and goals, including contradictory assumptions. -/
structure CheckRequest where
  source : FrenMir.CheckRequest
  assumptions : Array Body
  question : Question
  demand : Array Body
  deriving Repr, BEq

structure Program where
  mir : FrenMir.Theory
  declarations : Array Declaration
  requests : Array CheckRequest
  deriving Repr, BEq

-- Cheap laws about the actual constructors, without an evaluator model.
theorem branch_domain (c a b : Lowered) :
    (Lowered.branch c a b).defined = both c.defined (.ite c.value a.defined b.defined) := rfl

theorem bind_domain (binder : Token) (ty : FrenExpr.Ty) (v b : Lowered) :
    (Lowered.bind binder ty v b).defined =
      both v.defined (.letE binder ty v.value v.defined b.defined) := rfl

theorem strict_domain (op : BinaryOp) (a b : Lowered)
    (hd : op ≠ .div) (hm : op ≠ .mod) :
    (Lowered.binary op a b).defined = both a.defined b.defined := by
  cases op <;> simp_all [Lowered.binary, Lowered.defined, Verification.formula]

theorem call_domain (sig : Signature) (args : List Lowered) :
    (Lowered.call sig args).defined = both
      (args.foldr (fun a rest => both a.defined rest) (.bool true))
      (.app sig .domain (args.map (·.value))) := by
  have hf : (args.foldr (fun a rest => Verification.both a.verification rest) .empty).formula =
      args.foldr (fun a rest => both a.defined rest) (.bool true) := by
    induction args with
    | nil => rfl
    | cons a rest ih => exact congrArg (both a.defined) ih
  change both _ _ = both _ _
  rw [hf]
  rfl

theorem binary_verification (op : BinaryOp) (a b : Lowered)
    (hd : op ≠ .div) (hm : op ≠ .mod) :
    (Lowered.binary op a b).verification = .both a.verification b.verification := by
  cases op <;> simp_all [Lowered.binary]

theorem bind_verification (binder : Token) (ty : FrenExpr.Ty) (v b : Lowered) :
    (Lowered.bind binder ty v b).verification =
      .both v.verification (.letE binder ty v.value v.defined b.verification) := rfl

end FrenLir
