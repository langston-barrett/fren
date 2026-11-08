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

fren_test_runners textRunners

public def main (args : List String) : IO UInt32 := do
  if args == ["--job", "resolver"] then
    FrenAstToHirTests.runCases
    return 0
  if args == ["--job", "resolverProperties"] then
    FrenAstToHirTests.runProperties
    return 0
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
  unless args.isEmpty do return ← Fren.TextTests.cli textRunners args
  FrenAstToHirTests.runCases
  FrenAstToHirTests.runProperties
  FrenHirToThirTests.runCases
  FrenHirToThirTests.runAdmission
  FrenHirToThirTests.runOperators
  FrenHirToThirTests.runProperties
  Fren.SexpTests.run
  Fren.SexpTests.runDerive
  Fren.SexpTests.Phase.run
  return 0
