module

import FrenSexpTests

public def main : IO Unit := do
  Fren.SexpTests.run
  Fren.SexpTests.runDerive
  Fren.SexpTests.Phase.run
