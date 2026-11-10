module

public import FrenEvalTests.Support
import Plausible

public section
namespace FrenEvalTests
open FrenEval Plausible
open scoped Plausible.Decorations

structure Counts where
  admittedBase : Nat := 0
  defined : Nat := 0
  undefined : Nat := 0
  invalid : Nat := 0
  exhausted : Nat := 0
  rejected : Nat := 0
  rejectedProducer : Nat := 0
  mutations : Nat := 0
  deriving Repr, BEq

/-- Generated source is fed through the actual parser, resolver, typing and
both walking validators. Rejections and partial expressions are mandatory
premise classes, not discarded samples or supplied validity flags. -/
private def sample (n : Nat) (x y : Int) : Option Counts := do
  let offset := n % 41
  let source := "mod skeleton\nenum Light { Red, Amber, Green }\n" ++
    "fn sub(a: Int, b: Int): Int := a - b\n" ++
    s!"fn f(x: Int, y: Int): Int := let x := x + {offset} in if true then sub(x, y) else 1 div 0\n" ++
    "fn select(l: Light, x: Int): Int := match l { Light::Red => x, Light::Amber => 1 div 0, Light::Green => x + 1 }\n" ++
    "fn conjunction(x: Int, b?: Bool): Bool := b? and (x div 0 = 0)\n" ++
    "fn disjunction(x: Int, b?: Bool): Bool := b? or (x % 0 = 0)\n" ++
    s!"fn unusedLet(x: Int): Int := let y := x div 0 in x + {offset}\n" ++
    "fn usedLet(x: Int): Int := let y := x div 0 in y\n" ++
    "fn guarded(d: Int): Int := let y := 1 div d in if d != 0 then y else 0\n" ++
    "expect q(x: Int) { assume a: x <= 0 expect e: x div 0 = 0 }"
  let .ok p := fromSource ⟨n⟩ source | none
  let .ok actual := FrenHirToThir.checkWalkingSource ⟨n⟩ source | none
  if p.typed != actual || p.typed.resolved.document.emit != source then none else pure ()
  let defined := #[(result p "f" #[.int x, .int y], .int (x + offset - y)),
    (result p "select" #[light "Red", .int x], .int x),
    (result p "select" #[light "Green", .int x], .int (x + 1)),
    (result p "q" #[.int x] (some "a"), .bool (x ≤ 0)),
    (result p "conjunction" #[.int x, .bool false], .bool false),
    (result p "disjunction" #[.int x, .bool true], .bool true),
    (result p "unusedLet" #[.int x], .int (x + offset)),
    (result p "guarded" #[.int 0], .int 0), (result p "guarded" #[.int 1], .int 1)]
  if defined.any (fun (o, v) => !hasValue o v) then none else pure ()
  let undefined := #[result p "select" #[light "Amber", .int x],
    result p "conjunction" #[.int x, .bool true],
    result p "disjunction" #[.int x, .bool false], result p "usedLet" #[.int x],
    result p "q" #[.int x] (some "e")]
  if undefined.any (fun o => !isUndefined o) then none else pure ()
  if !isInvalid (result p "f" #[.int x]) ||
      !isInvalid (result p "f" #[.bool false, .int y]) ||
      !isInvalid (result p "select" #[.enum (key "Other") ((key "Other").named "Red"), .int x]) ||
      !isInvalid (result p "select" #[.enum (key "Light") ((key "Light").named "Absent"), .int x]) then
    none else pure ()
  if !isExhausted (result p "f" #[.int x, .int y] none 1) then none else pure ()
  let negatives := #[source.replace "x + 1" "false", -- ill-typed unselected arm
    source.replace "Light::Green => x + 1" "Light::Red => x + 1", -- duplicate/missing
    source ++ "\nfn loop(x: Int): Int := loop(x)",
    source ++ "\nfn value(dummy: Int): Int := sub",
    source ++ "\nfn bad(dummy: Int): Int := _"]
  if negatives.any (fun text => (fromSource ⟨n⟩ text).isOk) then none else pure ()
  if (fromResolved {p.input with references := #[]}).isOk then none else pure ()
  -- A distinct actual producer output implements the intentionally wrong op.
  let .ok mutant := fromSource ⟨n⟩ (source.replace "a - b" "a + b") | none
  if !hasValue (result mutant "f" #[.int x, .int 1]) (.int (x + offset + 1)) ||
      hasValue (result mutant "f" #[.int x, .int 1]) (.int (x + offset - 1)) then none else pure ()
  return ⟨1, defined.size, undefined.size, 4, 1, 5, 1, 1⟩

private def audit (n : Nat) (x y : Int) : Bool :=
  (sample n x y).any (· == ⟨1, 9, 5, 4, 1, 5, 1, 1⟩)

private def primitives (a b : Int) : Bool :=
  (match binary .add (.int a) (.int b) with
    | .ok (.int sum) => sum == a + b
    | _ => false) &&
  match binary .sub (.int a) (.int b), binary .div (.int a) (.int b), binary .rem (.int a) (.int b) with
  | .ok (.int difference), q, r =>
    difference == a - b &&
    if b == 0 then (match q, r with | .error .undefined, .error .undefined => true | _, _ => false)
    else match q, r with
      | .ok (.int quotient), .ok (.int remainder) =>
        a == quotient * b + remainder && 0 ≤ remainder && remainder < b.natAbs
      | _, _ => false
  | _, _, _ => false

private def checkProperty (p : Prop)
    (decorated : Decorations.DecorationsOf p := by mk_decorations) [Testable decorated] : IO Unit := do
  let report ← Testable.checkIO decorated {numInst := 100, maxSize := 35, randomSeed := some 20261111}
  IO.println s!"actual evaluator Plausible: {report}"
  match report with
  | .success _ => pure ()
  | _ => throw (IO.userError "actual evaluator Plausible failure")

def runProperties : IO Unit := do
  checkProperty <| ∀ (n : Nat) (x y : Int), audit n x y = true
  checkProperty <| ∀ (a b : Int), primitives a b = true
  let mut counts : Counts := {}
  for n in [:24] do
    let some c := sample n (-(n : Int)) (n + 1) | throw (IO.userError s!"premise sample {n} failed")
    counts := ⟨counts.admittedBase + c.admittedBase, counts.defined + c.defined,
      counts.undefined + c.undefined, counts.invalid + c.invalid, counts.exhausted + c.exhausted,
      counts.rejected + c.rejected, counts.rejectedProducer + c.rejectedProducer, counts.mutations + c.mutations⟩
  require (counts == ⟨24, 216, 120, 96, 24, 120, 24, 24⟩) "vacuous evaluator premise census"
  IO.println s!"actual evaluator premise census: {repr counts}; discarded=0; finite evidence only"

end FrenEvalTests
