module

public import FrenMir

public section
namespace FrenLir
open FrenModule FrenAst

/-- Both symbols of a definition take ordinary positional values. Domain is
semantic definedness of its body, never a solver success or fuel predicate. -/
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
Arithmetic values are total symbolic terms; domain formulas guard div/mod.
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

structure Lowered where
  value : Term
  defined : Term
  deriving Repr, BEq

/-- These are the actual lowering combinators. Boolean conjunction here is
logical conjunction of total formulas; source demand is encoded explicitly. -/
@[expose] def both (a b : Term) : Term := .binary .and a b

@[expose] def Lowered.binary (op : BinaryOp) (a b : Lowered) : Lowered :=
  let rightDemand := match op with
    | .and => Term.ite a.value b.defined (.bool true)
    | .or => Term.ite a.value (.bool true) b.defined
    | _ => b.defined
  let operands := both a.defined rightDemand
  let domain := match op with
    | .div | .mod => both operands (.binary .ne b.value (.int 0))
    | _ => operands
  ⟨.binary op a.value b.value, domain⟩

@[expose] def Lowered.branch (c yes no : Lowered) : Lowered :=
  ⟨.ite c.value yes.value no.value, both c.defined (.ite c.value yes.defined no.defined)⟩

@[expose] def Lowered.bind (binder : Token) (type : FrenExpr.Ty) (v body : Lowered) : Lowered :=
  ⟨.letE binder type v.value v.defined body.value,
    .letE binder type v.value v.defined body.defined⟩

@[expose] def Lowered.call (sig : Signature) (args : List Lowered) : Lowered :=
  let values := args.map (·.value)
  ⟨.app sig .value values,
    both (args.foldr (fun a rest => both a.defined rest) (.bool true)) (.app sig .domain values)⟩

@[expose] def Lowered.mark (origin : Origin) (v : Lowered) : Lowered :=
  ⟨.at origin v.value, .at origin v.defined⟩

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

/-- No query is asserted or discharged here. Demand roots stay independent of
Boolean assumptions and goals, including for contradictory assumptions. -/
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
    (Lowered.bind binder ty v b).defined = .letE binder ty v.value v.defined b.defined := rfl

theorem strict_domain (op : BinaryOp) (a b : Lowered)
    (ha : op ≠ .and) (ho : op ≠ .or) (hd : op ≠ .div) (hm : op ≠ .mod) :
    (Lowered.binary op a b).defined = both a.defined b.defined := by
  cases op <;> simp_all [Lowered.binary]

theorem call_domain (sig : Signature) (args : List Lowered) :
    (Lowered.call sig args).defined = both
      (args.foldr (fun a rest => both a.defined rest) (.bool true))
      (.app sig .domain (args.map (·.value))) := rfl

end FrenLir
