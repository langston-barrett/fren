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

structure Program where
  oir : FrenOir.Program
  queries : Array Query
  deriving Repr

structure Limits where
  wallMs : Nat := 2000
  solverMs : Nat := 1000
  solverResources : Nat := 1000000
  outputBytes : Nat := 65536
  inputBytes : Nat := 1048576
  deriving Repr

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
  deriving Repr

structure Result where
  query : Query
  outcome : Outcome
  receipt : Option Receipt
  deriving Repr

end FrenOirToSmt
