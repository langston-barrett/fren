module

public import FrenOir

public section
namespace FrenOirToSmt

inductive Failure where
  | unsupported (reason : String)
  | resourceExhausted (reason : String)
  | invalid (reason : String)
  deriving Repr, BEq

inductive Outcome where
  | sat
  | unsat
  | unknown (reason : String)
  | unsupported (reason : String)
  | resourceExhausted (reason : String)
  | error (reason : String)
  deriving Repr, BEq

structure Query where
  question : FrenOir.Question
  script : Except Failure String
  deriving Repr

@[expose] def sameExcept [BEq α] [BEq β] : Except α β → Except α β → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

instance : BEq Query where
  beq a b := a.question == b.question && sameExcept a.script b.script

structure Program where
  oir : FrenOir.Program
  queries : Array Query
  deriving Repr, BEq

structure Limits where
  wallMs : Nat := 2000
  solverMs : Nat := 1000
  solverResources : Nat := 1000000
  outputBytes : Nat := 65536
  inputBytes : Nat := 1048576
  deriving Repr, BEq

/-- A transport receipt is raw process evidence, not a source confirmation. -/
structure Receipt where
  command : Array String
  exitCode : Option Int
  stdout : String
  stderr : String
  stdoutHex : String
  stderrHex : String
  elapsedMs : Nat
  reason : String
  outcome : Outcome
  request : String := ""
  binding : String := ""
  kind : String := ""
  limits : Limits := {}
  deriving Repr, BEq

structure Result where
  query : Query
  outcome : Outcome
  receipt : Option Receipt
  deriving Repr

end FrenOirToSmt
