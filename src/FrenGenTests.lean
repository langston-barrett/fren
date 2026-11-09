module

public import FrenGen
meta import FrenGen

/-! Build-time checks of the THIR generator itself, on seeded samples: well
scoped, every origin in its item's table and used once, and a fault, when one
is asked for, recorded only as that fault. -/

namespace FrenGenTests
open FrenExpr FrenModule.Core FrenGen.Thir

/-- Every origin a body's nodes, binders and patterns use, in postorder. -/
private def origins : Expr .thir → List OriginId :=
  Expr.fold fun o _ n =>
    let own := match n with
      | .letE b _ _ => [b.origin]
      | .matchE _ arms => arms.toList.map (·.1.origin)
      | _ => []
    n.children.foldl (· ++ ·) [] ++ own ++ [o]

private def itemOrigins : Item (Expr .thir) → List OriginId
  | .enum e _ => [e.origin]
  | .function f _ => f.origin :: f.params.toList.map (·.origin) ++ origins f.body
  | .check c _ => c.origin :: c.params.toList.map (·.origin) ++
      c.members.toList.flatMap fun mem => mem.origin :: origins mem.body

/-- Origins are in range of their item's table and no two uses share one. -/
private def originsWellFormed (m : Thir) : Bool :=
  m.items.all fun item =>
    let used := itemOrigins item
    used.all (· < item.origins.size) && used.eraseDups.length == used.length

private def sample (seed : Nat) (fault : Option Fault) : Case := (seeded seed (seed % 12) fault).1

#guard (List.range 40).all fun seed =>
  let c := sample seed none
  c.expected.isNone && c.hir.scoped && originsWellFormed c.thir

#guard (List.range 20).all fun seed => Fault.all.all fun f =>
  let c := sample seed (some f)
  (c.expected.all (·.fault == f)) && originsWellFormed c.thir &&
    c.hir.scoped == (c.expected.map (·.fault) != some .dangling)

-- Seeded generation is a function of its seed; different seeds differ.
#guard (sample 5 none).thir.toSexp true == (sample 5 none).thir.toSexp true
#guard !((List.range 10).all fun s => (sample s none).thir.same (sample 0 none).thir)

end FrenGenTests
