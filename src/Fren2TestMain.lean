module

meta import FrenBaseTests.Properties
meta import FrenSourceTests.Properties
import FrenSexpTests

public def main : IO Unit := do
  Fren.SexpTests.run
  Fren.SexpTests.runDerive
  Fren.SexpTests.Phase.run
