-- keep-sorted start
import FrenCli.Enumerate
import FrenTest.OutOfFuel
-- keep-sorted end

/-! Runtime regressions for `eval::expression_limit`. Construct the deep
fixtures after startup: compiling a deep fixture in a module initializer
can itself overflow the main thread's stack before any job starts. -/

namespace Fren.Test.EvalLimits

open FrenCli.Eval
open Fren.Core.Enumeration
open Fren.Test.OutOfFuel (nots downInterp)

/-- Transport through definitions, vector constructors and packed binders
agrees at the last supported step, before and after compilation. -/
def depthTransportChecks : IO (Array String) := do
  let extra := (← IO.monoMsNow) % 1
  let failures ← IO.mkRef (#[] : Array String)
  let check (ok : Bool) (message : String) : IO Unit := do
    unless ok do failures.modify (·.push message)
  let yes : Ex := .lit (.bool true)
  let no : Ex := .lit (.bool false)
  let base : Look := fun n =>
    if n == `x then some (.bool false)
    else if n == `a || n == `b then some (.bool true) else none
  let definitions : Lean.Name → Option Ex := fun n =>
    if n == `y then some (.var `x) else if n == `z then some (.var `y) else none
  let I : Interp := { lookup? := some (readDefinedBody {} base definitions) }
  for (name, need) in [(`x, 1), (`y, 2), (`z, 3)] do
    check ((Ex.var name).eval I base (depth := need) == some (.bool false))
      s!"definition {name} spent its lookup twice"
    check (((Ex.var name).eval I base (depth := need - 1)).isNone)
      s!"definition {name} omitted its lookup step"
    check (readDefined {} base definitions need name == some (.bool false))
      s!"direct lookup {name} differs from expression lookup"
    check ((readDefined {} base definitions (need - 1) name).isNone)
      s!"direct lookup {name} did not spend its reference step"
  let shared : Ex := .memo #[nots (maxEvalDepth - 3) (.var `x)]
    (.table 0 #[(0, some yes, .shared 0)] none)
  check (shared.eval I base (depth := maxEvalDepth - 1) == some (.bool true))
    "a cache wrapper or read spent a synthetic expression step"
  check ((shared.eval I base (depth := maxEvalDepth - 2)).isNone)
    "a shared expression exceeded its caller's allowance"
  let helper := (List.range (2048 + extra)).foldl (fun body _ => Ex.memo #[] body) yes
  check ((helper.eval {} base).isNone) "raw cache helpers evaded the native depth guard"
  let vector : Ex := .ctor Fren.Core.matchVectorPath 0 #[.var `a, .var `b]
  let m : Ex := .match vector
    #[(.ctor 0 #[.bool true, .bool true], none, yes), (.wild, none, no)] 0 #[] none none
  for e in [m, .dispatch #[#[0, 1]] m] do
    for e in [e, e.compile (fun _ => none) (some [])] do
      check ((e.eval {} base (depth := 2)).isNone) "a match vector skipped its constructor step"
      check (e.eval {} base (depth := 3) == some (.bool true)) "a match vector spent an extra step"
  let domain : Interp := {
    domain := fun _ => some (#[.bool false, .bool true], true)
    fn := fun _ _ => some (.bool false) }
  for count in [1, 2, 3] do
    let names := (Array.range count).map fun k => Lean.Name.mkSimple s!"q{k}"
    let types := Array.replicate count ({ ty := .bool } : Fren.Core.PTy)
    for (leaf, lifted) in [(Ex.var `x, false), (Ex.app `value #[], true)] do
      let body := nots (maxEvalDepth - count - 1) leaf
      let q : Ex := .quant 0 0 true names (Array.replicate count none) types body
      let compiled := q.compile (fun _ => none) (some [])
      if lifted then
        check (compiled matches .lifted ..) "quantifier regression did not exercise lifted values"
      for e in [q, compiled] do
        check ((e.eval domain base).isSome) "a quantifier body lost its boundary allowance"
        check ((e.eval domain base (depth := maxEvalDepth - 1)).isNone)
          "a quantifier body omitted a real binder step"
  let cold := nots (2048 + extra) (.var `x)
  for e in [Ex.memo #[cold] (.table 0 #[(0, none, yes)] none),
      .lifted #[#[cold]] (.quant 0 0 true #[`b] #[none] #[{ ty := .bool }] yes)] do
    check (!e.withinLimits) "a cache hid an oversized operand from admission"
    check (((e.compile (fun _ => none) (some [])).eval domain base).isNone)
      "compilation traversed an oversized cached operand before admission"
  return ← failures.get

def check : IO (Array String) := do
  let extra := (← IO.monoMsNow) % 1
  let failures ← IO.mkRef (#[] : Array String)
  let check (ok : Bool) (message : String) : IO Unit := do
    unless ok do failures.modify (·.push message)
  -- Charge queued nodes before constructing the next work-list segment.
  -- Repeated wide children otherwise pile up beyond the node allowance
  -- before the depth limit is reached.
  let layers ← IO.mkRef 0
  let wide ← expressionInfoM (fun (n : Nat) => do
    layers.modify (· + 1)
    return { children := Array.replicate 20000 (n + 1) }) 0
  check (wide.isNone && (← layers.get) ≤ 211)
    "expression admission queued more nodes than its remaining budget"
  let yes : Ex := .lit (.bool true)
  let no : Ex := .lit (.bool false)
  let boundaryMatch : Ex := .match yes #[(.wild, none, nots (maxEvalDepth - 2) yes)] 0 #[] none none
  check (boundaryMatch.withinLimits && (Ex.dispatch #[#[0]] boundaryMatch).withinLimits)
    "constructor dispatch changed admission at the depth boundary"
  -- A selected unknown body used to be retried by the partial-case
  -- fallback, doubling the work at every level. Unknown scrutinees and
  -- guards must not restart nested evaluations either. Keep the leaf open
  -- so compilation cannot fold away the regression.
  let wraps : Array (String × (Ex → Ex)) := #[
    ("match body", fun body => .match yes #[(.wild, none, body)] 0 #[] none none),
    ("table body", fun body => .table 0 #[(0, some yes, body)] none),
    ("dispatch body", fun body => .dispatch #[#[0]]
      (.match (.ctor `Case 0 #[]) #[(.ctor 0 #[], none, body)] 0 #[] none none)),
    ("match scrutinee", fun scrutinee => .match scrutinee
      #[(.bool true, none, yes), (.bool false, none, no)] 0 #[] none none),
    ("match guard", fun guard => .match yes
      #[(.wild, some guard, yes), (.wild, none, no)] 0 #[] none none),
    ("table guard", fun guard => .table 0 #[(0, some guard, yes), (0, none, no)] none),
    ("match vector", fun scrutinee => .match (.ctor Fren.Core.matchVectorPath 0 #[scrutinee, yes])
      #[(.ctor 0 #[.bool true, .bool true], none, yes), (.wild, none, no)] 0 #[] none none)]
  for (label, wrap) in wraps do
    for (leaf, expected) in [(Ex.var `missing, none), (yes, some (Val.bool true))] do
      let nested := (List.range (40 + extra)).foldl (fun body _ => wrap body) leaf
      check (nested.eval {} (fun _ => none) == expected) s!"{label} changed its value"
      check ((nested.compile (fun _ => none) (some [])).eval {} (fun _ => none) == expected)
        s!"compiled {label} changed its value"
  for (label, wrap) in wraps.extract 0 3 do
    let call : Ex := .app `caseLoop #[]
    let I : Interp := { recDefs := fun _ => some (#[], wrap call) }
    check ((call.eval I (fun _ => none)).isNone) s!"{label} retried a depth-limited recursion"
  -- A single cache budget left every shared read below it uncached.
  -- Nested additions then expanded to 2^40 evaluations despite sharing.
  for leaf in [Ex.lit (.int 0), .var `missing] do
    let additions := (List.range (40 + extra)).foldl
      (fun body _ => Ex.memo #[body] (.bin .add (.shared 0) (.shared 0))) leaf
    check (additions.eval {} (fun _ => none) == leaf.eval {} (fun _ => none))
      "depth-sensitive memoization repeated a shared expression"
  let keyed := Memo.ofFn (evalDepth + extra) fun d => some (.int d)
  for d in [0:evalDepth + 2] do
    check (keyed.get d == some (.int (min d evalDepth))) "a memo reused another depth's result"
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
  let far : Int := 1 <<< (80 + extra)
  for (label, pattern, expected) in [
      ("sparse natural", Fren.Core.Pat.or #[.int none (some 0), .int (some far) (some far)], #[0, far]),
      ("negative prefix", .int (some (-far)) (some 0), #[0])] do
    let t : Fren.Core.PTy := { ty := .nat, pat? := some pattern }
    check (pattern.intValuesWithin? maxTypeNodes (some 0) == some expected)
      s!"{label} did not construct exactly its admitted intervals"
    check (Fren.Core.PTy.values (fun _ => none) t 2 == some (expected.map Fren.Core.PVal.int))
      s!"{label} materialized a discarded prefix or gap"
    match shapeOf (fun _ => none) 1 t with
    | .ok (.ints values) => check (values.toArray == expected) s!"{label} changed the domain"
    | _ => check false s!"{label} did not enumerate its tiny finite domain"
  -- A shallow generic root used to call unbounded PTy.subst on this field
  -- before checking its depth. Test both explicit and missing PTy metadata.
  let raw := (List.range (2048 + extra)).foldl (fun t _ => Fren.Core.Ty.seq t) (.param 0 `A)
  let generic : Fren.Core.PTy := { ty := .record `Generic [.bool], elems := #[{ ty := .bool }] }
  let deepField := (List.range (2048 + extra)).foldl
    (fun t _ => ({ ty := .seq t.ty, elems := #[t] } : Fren.Core.PTy)) { ty := .param 0 `A }
  for field in [deepField, ({ ty := raw } : Fren.Core.PTy)] do
    let data : Fren.Core.DataShape := { parts := #[#[field]], isRecord := true }
    let shapes := fun _ => some data
    check ((instantiateWithin data generic).isNone) "generic substitution escaped its budget"
    check ((instantiateWithin data generic 1000000 1000000).isNone) "requested instantiation limits bypassed the cap"
    let spec : Spec := { shapes := ({} : Lean.NameMap Fren.Core.DataShape).insert `Generic data }
    check (((Ex.typed generic #[] yes).appsOf spec).contains FrenCli.typeResourceLimit)
      "enumeration dependency discovery substituted an oversized generic"
    check ((shapeOf shapes 1 generic).toOption.isNone) "generic fields escaped type admission"
    check ((typeHoldsAt shapes evalDepth generic (.ctor `Generic 0 #[.seq #[]])).isNone)
      "structural membership substituted an oversized field"
    let I : Interp := { shapes }
    check (((Ex.typed generic #[] (.ctor `Generic 0 #[.seqLit #[]])).eval I (fun _ => none)).isNone)
      "invariant membership substituted an oversized field"
    check ((!invariantFreeWithin shapes generic)) "compilation inspected an oversized generic before admission"
    check ((((Ex.typed generic #[] (.ctor `Generic 0 #[.seqLit #[]])).compile shapes (some [])).eval I (fun _ => none)).isNone)
      "compilation substituted an oversized generic before membership"
  let unused : Fren.Core.DataShape := { parts := #[#[{ ty := .bool }]], isRecord := true }
  let unusedArgument := (List.range (2048 + extra)).foldl (fun t _ => Fren.Core.Ty.seq t) .bool
  let deepArgument : Fren.Core.PTy := { ty := .record `Generic [unusedArgument] }
  check ((instantiateWithin unused deepArgument).isNone) "an unused generic argument escaped type admission"
  check ((shapeOf (fun _ => some unused) 1 deepArgument).toOption.isNone)
    "an encoder could receive an oversized unused generic argument"
  -- The adapter must not recursively fill missing metadata before Core
  -- sees even an unconstrained variable's raw declared type.
  let slot : FrenCli.CVar :=
    { name := `x, role := .input, isPub := false
      ty := .bool, span := default, ptype := { ty := unusedArgument } }
  let comp : FrenCli.CComp :=
    { path := `deepVariable, file := 0, span := default
      vars := #[slot], props := #[] }
  let evalComp : Comp := { path := comp.path, vars := #[], constraints := #[], insts := #[] }
  check ((FrenCli.enumerateComp {} evalComp comp #[] "deep variable").toOption.isNone)
    "the command-line adapter expanded metadata before type admission"
  let tiny : Fren.Core.DataShape := { parts := #[#[{ ty := .param 0 `A }]], isRecord := true }
  check ((instantiateWithin tiny generic).isSome) "bounded substitution rejected an ordinary generic"
  let separated := Fren.Core.Pat.or ((Array.range (8192 + extra)).map fun (k : Nat) =>
    .int (some (2 * (k : Int))) (some (2 * (k : Int))))
  check (separated.intCount? == some (8192 + extra)) "interval merging recursed through preceding gaps"
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
  let coerced := nots (maxEvalDepth - 1 + extra) (.bin .eq yes yes)
  check coerced.withinLimits "a Boolean coercion consumed an extra level"
  let aliases := (List.range (2048 + extra)).foldl (fun body _ => Ex.bin .eq body yes) yes
  check (aliases.eval {} (fun _ => none) == some (.bool true)) "Boolean coercions retained native frames"
  check ((aliases.compile (fun _ => none) (some [])).eval {} (fun _ => none) == some (.bool true))
    "compiling Boolean coercions retained native frames"
  check ((coerced.eval {} (fun _ => none)).isSome) "a Boolean coercion lost its last depth"
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
  -- The enumerator also evaluates raw recursive bodies: sharing must not
  -- depend on compiling a body into memo instructions first.
  for op in [Op.and, .or, .add] do
    let zero := if op == .add then Ex.lit (.int 0) else yes
    let call : Ex := .app `duplicate #[.bin .sub (.bound `n) (.lit (.int 1))]
    let body : Ex := .ite (.bin .le (.bound `n) (.lit (.int 0))) zero (.bin op call call)
    let I : Interp := { recDefs := fun _ => some (#[`n], body) }
    let result := (Ex.app `duplicate #[.lit (.int (40 + extra))]).eval I (fun _ => none)
    check result.isSome "a raw recursive body repeated identical calls"
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
  -- Main's giving-site obligations use the same remaining budget as
  -- whole-type invariants, including a nested obligation's last step.
  let obligation : Fren.Core.Cons := .predicate { name := `bounded, predicate := `bounded }
  let I : Interp := { defs := fun _ => some (#[`x], nots (32 + extra) yes, .bool) }
  let callCheck : Ex := .obligation obligation (.lit (.int extra))
  check (callCheck.eval I (fun _ => none) == some (.bool true))
    "a giving-site invariant lost its value within the depth budget"
  check ((callCheck.eval I (fun _ => none) (depth := 4)).isNone)
    "a giving-site invariant reset the depth budget"
  let nestedCheck : Ex := .obligation (.newtype `Box .atLeast0) (.lit (.int extra))
  check ((nestedCheck.eval {} (fun _ => none) (depth := 2)).isNone)
    "a nested giving-site obligation panicked at the depth boundary"
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
  check (!quant.withinLimits) "packed binders evaded expression-depth admission"
  check ((quant.eval {} (fun _ => none)).isNone) "quantifier binders exceeded the depth limit"
  return (← failures.get) ++ (← depthTransportChecks)

end Fren.Test.EvalLimits
