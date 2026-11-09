module

public import FrenLir

public section
namespace FrenOir
open FrenLir FrenModule FrenAst

/-- Complete mathematical domains, never a finite search bound on Int. Enum
constructors retain their nominal owner and canonical declaration order. -/
inductive Domain where
  | boolean
  | integer
  | enumeration (owner : FrenBase.ItemId) (constructors : Array FrenBase.ItemId)
  deriving Repr, BEq

/-- A parameter is a total value of its complete domain. Its LIR local domain
component is true; this is an interpretation rule, not a block hypothesis. -/
structure Parameter where
  source : TypedParameter
  domain : Domain
  deriving Repr, BEq

/-- Frames are outermost first. Folding them back around a condition preserves
interleaved guards and value/domain lets without shifting open terms. -/
inductive Frame where
  | guard (condition : Term) (positive : Bool)
  | binding (binder : Token) (type : FrenExpr.Ty) (value domain : Term)
  deriving Repr, BEq

@[expose] def Frame.wrap (frame : Frame) (body : Term) : Term :=
  match frame with
  | .guard c positive => .binary .and (if positive then c else .unary .not c) body
  | .binding name ty value domain => .letE name ty value domain body

@[expose] def inScope (frames : List Frame) (body : Term) : Term :=
  frames.foldr Frame.wrap body

@[expose] def conjunction (terms : Array Term) : Term :=
  terms.foldr (fun a rest => .binary .and a rest) (.bool true)

inductive Kind where
  | functionDefinedness
  | assumptionDefinedness
  | goalDefinedness
  | assumptionsSatisfiable
  | validity
  deriving Repr, BEq, DecidableEq

/-- Edges name actual generated question IDs or actual definition equations.
No edge is a supplied proof or a solver answer. -/
inductive Dependency where
  | question (id : Nat)
  | definition (id : FrenBase.ItemId)
  deriving Repr, BEq

/-- `ready` means the dependency rule is supported, never that a question or
its dependencies have been proved. This unit has no aggregate success result. -/
inductive Readiness where
  | ready
  | unresolved (reason : String)
  deriving Repr, BEq

structure Question where
  id : Nat
  kind : Kind
  owner : FrenBase.ItemId
  parameters : Array Parameter
  context : TypeContext
  request : Option Nat
  subject : Option TypedBody
  origin : Option Origin
  path : List Nat
  hypotheses : Array Body
  frames : List Frame
  condition : Term
  dependencies : Array Dependency
  readiness : Readiness
  deriving Repr, BEq

/-- Sat searches for the hypotheses. All other questions search for a failure
of their condition. Hypotheses live outside local frames: no variable capture
and no let-bound assumption can escape as a global premise. -/
@[expose] def Question.search (q : Question) : Term :=
  let h := conjunction (q.hypotheses.map (·.term.value))
  if q.kind = .assumptionsSatisfiable then h
  else .binary .and h (inScope q.frames (.unary .not q.condition))

/-- Equations interpret both symbols by their actual retained LIR body in the
callee's ordered parameter context. A domain equation is not a totality axiom. -/
structure Definition where
  signature : Signature
  body : Body
  deriving Repr, BEq

@[expose] def Definition.value (d : Definition) : Term := d.body.term.value
@[expose] def Definition.domain (d : Definition) : Term := d.body.term.defined

structure Program where
  lir : FrenLir.Program
  enumerations : Array FrenMir.Enumeration
  definitions : Array Definition
  questions : Array Question
  deriving Repr, BEq

/-- No solver or model confirmation runs in this unit. Answer interpretation
classifies raw search evidence only. Even Unsat requires independently
established domains/dependencies before any source result may be reported. -/
inductive Answer where
  | sat
  | unsat
  | unknown (reason : String)
  | unsupported (reason : String)
  | resourceExhausted (reason : String)
  deriving Repr, BEq

inductive Evidence where
  | candidateWitness
  | candidateCounterexample
  | unsatisfiableAssumptionSearch
  | noCounterexample
  | unknown (reason : String)
  | unsupported (reason : String)
  | resourceExhausted (reason : String)
  deriving Repr, BEq

@[expose] def Question.interpret (q : Question) : Answer → Evidence
  | .sat => if q.kind == .assumptionsSatisfiable then .candidateWitness else .candidateCounterexample
  | .unsat => if q.kind == .assumptionsSatisfiable then .unsatisfiableAssumptionSearch else .noCounterexample
  | .unknown s => .unknown s
  | .unsupported s => .unsupported s
  | .resourceExhausted s => .resourceExhausted s

-- These are constructor laws about the actual formulas, not solver claims.
theorem scoped_binding (n : Token) (ty : FrenExpr.Ty) (v d c : Term) (rest : List Frame) :
    inScope (.binding n ty v d :: rest) c = .letE n ty v d (inScope rest c) := rfl

theorem scoped_guard (g c : Term) (rest : List Frame) :
    inScope (.guard g false :: rest) c = .binary .and (.unary .not g) (inScope rest c) := rfl

theorem search_counterexample (q : Question) (h : q.kind ≠ .assumptionsSatisfiable) :
    q.search = .binary .and (conjunction (q.hypotheses.map (·.term.value)))
      (inScope q.frames (.unary .not q.condition)) := by
  simp [Question.search, h]

end FrenOir
