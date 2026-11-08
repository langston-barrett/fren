module

public import FrenBase
public meta import FrenBase.Identity
import Std.Data.HashMap
meta import Std.Data.HashMap

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

namespace FrenBaseTests
open FrenBase

private def ids : List ItemId :=
  let f := ItemId.named .root "f"
  let g := ItemId.named .root "g"
  [ItemId.named f "{closure#0}", ItemId.generated f "closure" 0,
   ItemId.generated g "closure" 0, ItemId.generated f "other" 0,
   ItemId.generated f "closure" 1]

private def mapChecks : Bool := Id.run do
  let mut m : Std.HashMap ItemId Nat := {}
  for (id, i) in ids.zipIdx do
    m := m.insert id i
  let equalKey := ItemId.generated (ItemId.named .root "f") "closure" 0
  let found := m[equalKey]? == some 1 && m.size == 5
  m := m.insert equalKey 99
  return found && m.size == 5 && m[equalKey]? == some 99 &&
    (ids.zipIdx.all fun (id, i) => m[id]? == some (if i == 1 then 99 else i))

#guard mapChecks
#guard hash (ItemId.generated (ItemId.named .root "f") "closure" 0) ==
  hash (ItemId.generated (ItemId.named .root "f") "closure" 0)
#guard ItemId.root != ItemId.named .root ""
#guard ItemId.root.render == (ItemId.named .root "").render
#guard ItemId.named (ItemId.named .root "f") "{closure#0}" !=
  ItemId.generated (ItemId.named .root "f") "closure" 0
#guard (ItemId.named (ItemId.named .root "f") "{closure#0}").render ==
  (ItemId.generated (ItemId.named .root "f") "closure" 0).render
#guard ItemId.generated (ItemId.named .root "λ") "" 0 !=
  ItemId.generated (ItemId.named .root "λ") "λ.#{}" 0
#guard ItemId.generated (ItemId.named .root "λ") "λ.#{}" 0 !=
  ItemId.generated (ItemId.named .root "λ") "λ.#{}" 18446744073709551616
end FrenBaseTests
