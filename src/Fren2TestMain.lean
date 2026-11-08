module

meta import FrenBaseTests.Properties
meta import FrenBaseTests.Binding
meta import FrenSourceTests.Properties
import FrenSexpTests
import FrenTextDemo
import FrenAstTests
import FrenParseTests
import FrenAstToHirTests
import FrenHirToThirTests
import FrenEvalTests

fren_test_runners textRunners

public def main (args : List String) : IO UInt32 := do
  if args == ["--job", "resolver"] then
    FrenAstToHirTests.runCases
    return 0
  if args == ["--job", "resolverProperties"] then
    FrenAstToHirTests.runProperties
    return 0
  if args == ["--job", "walkingProperties"] then
    FrenHirToThirTests.runWalkingProperties
    return 0
  if args == ["--job", "walking"] then
    FrenHirToThirTests.runWalking
    return ← Fren.TextTests.cli textRunners ["--lib", "FrenWalking"]
  if args == ["--job", "typing"] then
    FrenHirToThirTests.runCases
    FrenHirToThirTests.runAdmission
    return 0
  if args == ["--job", "typingOperators"] then
    FrenHirToThirTests.runOperators
    return 0
  if args == ["--job", "typingProperties"] then
    FrenHirToThirTests.runProperties
    return 0
  if args == ["--job", "evaluator"] then
    FrenEvalTests.runCases
    return 0
  if args == ["--job", "evaluatorProperties"] then
    FrenEvalTests.runProperties
    return 0
  unless args.isEmpty do return ← Fren.TextTests.cli textRunners args
  FrenAstToHirTests.runCases
  FrenAstToHirTests.runProperties
  FrenHirToThirTests.runWalking
  let walkingText ← Fren.TextTests.cli textRunners ["--lib", "FrenWalking"]
  if walkingText != 0 then return walkingText
  FrenHirToThirTests.runWalkingProperties
  FrenHirToThirTests.runCases
  FrenHirToThirTests.runAdmission
  FrenHirToThirTests.runOperators
  FrenHirToThirTests.runProperties
  FrenEvalTests.runCases
  FrenEvalTests.runProperties
  Fren.SexpTests.run
  Fren.SexpTests.runDerive
  Fren.SexpTests.Phase.run
  return 0
