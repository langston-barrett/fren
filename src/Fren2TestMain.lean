module

meta import FrenBaseTests.Properties
meta import FrenBaseTests.Binding
meta import FrenSourceTests.Properties
import FrenSexpTests
import FrenTextDemo
import FrenAstTests
import FrenParseTests

fren_test_runners textRunners

public def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do return ← Fren.TextTests.cli textRunners args
  Fren.SexpTests.run
  Fren.SexpTests.runDerive
  Fren.SexpTests.Phase.run
  return 0
