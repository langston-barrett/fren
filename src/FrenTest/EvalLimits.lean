-- keep-sorted start
import FrenTest.OutOfFuel
-- keep-sorted end

/-! Runtime regressions for `eval::expression_limit`. Construct the deep
fixtures after startup: compiling a deep fixture in a module initializer
can itself overflow the main thread's stack before any job starts. -/

namespace Fren.Test.EvalLimits

open FrenCli.Eval
open Fren.Core.Enumeration
open Fren.Test.OutOfFuel (nots downInterp)

def check : IO (Array String) := do
  let extra := (← IO.monoMsNow) % 1
  let failures ← IO.mkRef (#[] : Array String)
  let check (ok : Bool) (message : String) : IO Unit := do
    unless ok do failures.modify (·.push message)
  let yes : Ex := .lit (.bool true)
  let many := 10000 + extra
  check (quantifiedTruth true true (fun (_ : Nat) => none) (List.range many) == none)
    "unknown quantifier instances retained recursive frames"
  check (quantifiedTruth true true (fun k => if k == many then some false else none)
      (List.range (many + 1)) == some false) "a late quantifier instance did not decide the result"
  let unknownDomain : Ex := .quant 0 0 true #[`x]
    #[some (.lit (.seq (Array.replicate many (.bool true))))] #[] (.var `missing)
  check ((unknownDomain.eval {} (fun _ => none)).isNone)
    "a large listed quantifier domain exceeded the recursion budget"
  check (!typesWithinLimits (fun _ => none)
    (Array.replicate (maxEvalDepth + extra) (1, ({ ty := .bool } : Fren.Core.PTy))))
    "too many enumeration slots evaded the recursion budget"
  let treeTy : Fren.Core.PTy := { ty := .enum `Branching [] }
  let branching : Fren.Core.DataShape := { parts := #[#[], #[treeTy, treeTy]], recursive := true }
  check ((shapeOf (fun _ => some branching) (18 + extra) treeTy).toOption.isNone)
    "type expansion exceeded its node budget"
  let wideEnum : Fren.Core.DataShape := { parts := Array.replicate (maxEvalDepth + extra) #[] }
  check ((shapeOf (fun _ => some wideEnum) 1 treeTy).toOption.isNone)
    "a wide constructor list exceeded the recursion budget"
  let fields := Array.replicate (maxEvalDepth + extra) ({ ty := .bool } : Fren.Core.PTy)
  let wideRecord : Fren.Core.DataShape := { parts := #[fields], isRecord := true }
  check ((shapeOf (fun _ => some wideRecord) 1 { ty := .record `Wide [] }).toOption.isNone)
    "a wide field list exceeded the recursion budget"
  let nested := (List.range (maxEvalDepth + extra)).foldl
    (fun t _ => ({ ty := .seq t.ty, elems := #[t] } : Fren.Core.PTy)) { ty := .bool }
  check ((shapeOf (fun _ => none) 1 nested).toOption.isNone) "type expansion exceeded its depth budget"
  let finite : Fren.Core.PTy := { ty := .int, pat? := some (.int (some 0) (some (Int.ofNat (maxTypeNodes + extra)))) }
  check ((shapeOf (fun _ => none) 1 finite).toOption.isNone) "a finite domain exceeded the allocation budget"
  let unbounded := { finite with pat? := some (.or #[.int (some 0) (some (1 <<< 80)), .wild false]) }
  check ((shapeOf (fun _ => none) 1 unbounded).isOk) "an unbounded pattern materialized an unused finite branch"
  for base in [0:8] do
    for exponent in [0:20] do
      check (boundedPower base exponent == min (base ^ exponent) (maxBehaviours + 1))
        "an interpretation count was not capped accurately"
  let huge := 1 <<< (64 + extra)
  check ((tablesBySize huge #[0, 0] maxBehaviours).isNone) "an oversized function table was constructed"
  check (tablesBySize huge #[0] maxBehaviours == some #[(0, 0)]) "a constant function materialized its domain"
  check (tablesBySize huge #[] maxBehaviours == some #[]) "an empty codomain materialized its domain"
  check ((tablesBySize 17 #[0, 0] (maxBehaviours * 10)).isNone) "a requested table limit bypassed the cap"
  check (tableEntry 1 0 huge == 0) "a constant table computed a needless power"
  let atLimit := nots (maxEvalDepth - 1 + extra) yes
  let beyond := nots (2048 + extra) yes
  check atLimit.withinLimits "an expression at the depth limit was rejected"
  check (!beyond.withinLimits) "the expression depth limit was not enforced"
  check (Ex.scalarTotal #[atLimit]) "a scalar formula within the budget lost the total backend"
  check (!Ex.scalarTotal #[beyond]) "an oversized scalar formula bypassed knownness checks"
  check (!Ex.scalarTotal #[.bin .div (.lit (.int 1)) (.lit (.int 0))])
    "a potentially undefined operation bypassed knownness checks"
  check ((atLimit.eval {} (fun _ => none)).isSome) "evaluation rejected the depth boundary"
  check ((beyond.eval {} (fun _ => none)).isNone) "evaluation exceeded the depth limit"
  check ((beyond.eval {} (fun _ => none) (depth := 1000000)).isNone)
    "a requested depth bypassed the evaluator's bound"
  check (((beyond.compile (fun _ => none) (some [])).eval {} (fun _ => none)).isNone)
    "compilation exceeded the depth limit"
  let wide : Ex := .seqLit (Array.replicate (maxEvalNodes + extra) yes)
  check ((Ex.seqLit (Array.replicate (maxEvalNodes - 1 + extra) yes)).withinLimits)
    "an expression at the node limit was rejected"
  check (!wide.withinLimits) "the expression node limit was not enforced"
  check (((wide.compile (fun _ => none) (some [])).eval {} (fun _ => none)).isNone)
    "compilation exceeded the node limit"
  let recur : Ex := .app `down #[.lit (.int (10000 + extra))]
  check ((recur.eval (downInterp 0 false) (fun _ => none)).isNone)
    "recursive applications reset the depth budget"
  let memoBody : Ex := .memo #[.app `memoLoop #[]] (nots (96 + extra) (.shared 0))
  let I : Interp := { recDefs := fun _ => some (#[], memoBody) }
  check (((Ex.app `memoLoop #[]).eval I (fun _ => none)).isNone)
    "forcing a shared expression restored its creator's depth budget"
  let shared : Ex := .memo #[nots (evalDepth / 2 + 6 + extra) yes] (.shared 0)
  check ((shared.eval {} (fun _ => none)).isSome)
    "a cache computed with a smaller depth budget hid a value within the caller's depth budget"
  let definition := nots (96 + extra) (.var `loop)
  check ((readDefined {} (fun _ => none) (fun _ => some definition) maxEvalDepth `loop).isNone)
    "reading a defined output reset the depth budget"
  let sum : Ex := .bin .add (.var `sum) (.lit (.int extra))
  check ((Ex.indicators? (fun _ => some sum) 10000 false (.var `sum)).isNone)
    "recognizing an expanded count reset the depth budget"
  let atom : Atom := { label := `e, pfx := `child, e := .var `x }
  let I : Interp := { lookup? := some fun _ n => if n == `child.x then some (.bool true) else none }
  check (atom.eval I (fun _ => none) == some true) "bounded lookup lost the atom's call prefix"
  let predicate : Fren.Core.PTy := { ty := .int, invariants := #[{ name := `loop, predicate := `loop }] }
  let I : Interp := { defs := fun _ => some (#[`x], .typed predicate #[] (.bound `x), .bool) }
  check (((Ex.typed predicate #[] (.lit (.int extra))).eval I (fun _ => none)).isNone)
    "invariant evaluation reset the depth budget"
  let tree : Fren.Core.PTy := { ty := .enum `Tree [] }
  let value := (List.range (2048 + extra)).foldl (fun v _ => Val.ctor `Tree 1 #[v]) (.ctor `Tree 0 #[])
  let I : Interp := { shapes := fun _ => some { parts := #[#[], #[tree]] } }
  check (((Ex.typed tree #[] (.lit value)).eval I (fun _ => none)).isNone)
    "value membership exceeded the depth limit"
  let deepDomain : Ex := .quant 0 0 true #[`x] #[some (.lit (.seq #[value]))] #[tree] yes
  check (((deepDomain.compile I.shapes (some [])).eval I (fun _ => none)).isNone)
    "compiling a quantifier traversed or discarded an oversized domain value"
  let refined : Fren.Core.PTy := { tree with invariants := #[{ name := `unknown, predicate := `unknown }] }
  let I : Interp := { shapes := fun _ => some { parts := #[#[{ ty := .nat }]] } }
  let invalid : Ex := .typed refined #[] (.lit (.ctor `Tree 0 #[.int (-1 - extra)]))
  check (invalid.eval I (fun _ => none) == some (.bool false))
    "an unknown outer invariant hid an invalid nested natural"
  let count := maxEvalDepth + extra
  let names := (Array.range count).map fun k => Lean.Name.mkSimple s!"x{k}"
  let domains := Array.replicate count (some (Ex.seqLit #[yes]))
  let quant : Ex := .quant 0 0 true names domains #[] yes
  check ((quant.eval {} (fun _ => none)).isNone) "quantifier binders exceeded the depth limit"
  return ← failures.get

end Fren.Test.EvalLimits
