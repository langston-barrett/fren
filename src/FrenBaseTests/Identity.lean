module

public import FrenBase
public meta import FrenBase.Identity

namespace FrenBaseTests
open FrenBase

private def f := ItemId.named .root "f"
private def g := ItemId.named .root "g"

#guard (ItemId.generated f "closure" 0).render == "f.{closure#0}"
#guard (ItemId.generated g "closure" 0).render == "g.{closure#0}"
#guard ItemId.named f "x" != ItemId.named g "x"
#guard ItemId.generated f "closure" 0 != ItemId.generated f "other" 0
#guard ItemId.generated f "closure" 0 != ItemId.generated f "closure" 1
#guard ItemId.named f "{closure#0}" != ItemId.generated f "closure" 0
#guard ItemId.root.parent == none
#guard ItemId.root.component == none
#guard (ItemId.named f "").components == [.named "f", .named ""]
#guard (ItemId.generated f "a.#{}λ" 1000000).component == some (.generated "a.#{}λ" 1000000)

/-- Run a small deterministic smoke check for a future test driver. -/
public def run : IO Unit := do
  unless (ItemId.generated f "closure" 0).render == "f.{closure#0}" &&
      ItemId.generated f "closure" 0 != ItemId.generated g "closure" 0 do
    throw <| IO.userError "item identity smoke check failed"
end FrenBaseTests
