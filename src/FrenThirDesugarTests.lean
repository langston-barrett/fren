module

public import FrenThirDesugar
public import FrenEval
import Plausible

public section
namespace FrenThirDesugarTests
open FrenThirDesugar FrenEval Plausible
open scoped Plausible.Decorations

@[expose] def evaluator (p : FrenThirDesugar.Program) : FrenEval.Program := ⟨p.input, p.typed, p.accepted⟩

/-- The actual interpreter receives the same program, request, arguments and
operational depth. This includes the complete failure or evaluation payload. -/
theorem evaluation (p : FrenThirDesugar.Program) (r : Request) (v : Array Value) (depth : Nat) :
    evaluate (evaluator (desugar p)) r v depth = evaluate (evaluator p) r v depth := rfl

private def key (s : String) : FrenBase.ItemId := FrenBase.ItemId.root.named "skeleton" |>.named s
private def light (s : String) : Value := .enum (key "Light") ((key "Light").named s)
private def source : String := "pub mod skeleton\n\n\
  pub enum Light { Red, Amber, Green }\n\
  pub fn next(l: Light): Light := match l { Light::Red => Light::Green, Light::Green => Light::Amber, Light::Amber => Light::Red, }\n\
  pub fn wait(l: Light, base: Int): Int := match l { Light::Red => base + 30, Light::Amber => base + 5, Light::Green => base, }\n\
  fn partial(x: Int): Int := x div 0\n\
  fn unused(x: Int): Int := if true then x else 1 div 0\n\
  fn unusedLet(dummy: Int): Int := let x := 1 div 0 in 0\n\
  fn usedLet(dummy: Int): Int := let x := 1 div 0 in x\n\
  fn guarded(d: Int): Int := let x := 1 div d in if d != 0 then x else 0\n\
  fn conjunction(b?: Bool): Bool := b? and (1 div 0 = 0)\n\
  fn disjunction(b?: Bool): Bool := b? or (1 % 0 = 0)\n\
  fn nested(dummy: Int): Int := let x := 1 div 0 in let y := x + 1 in 4\n\
  fn nestedUsed(dummy: Int): Int := let x := 1 div 0 in let y := x + 1 in y\n\
  fn shadow(dummy: Int): Int := let x := 1 div 0 in let x := 8 in x\n\
  fn capture(x: Int): Int := let y := x + 1 in let x := 100 in y\n\
  fn strictIff(b?: Bool): Bool := b? iff (1 div 0 = 0)\n\
  fn strictEq(b?: Bool): Bool := b? = (1 div 0 = 0)\n\
  fn strictNe(b?: Bool): Bool := b? != (1 div 0 = 0)\n\
  fn first(x: Int, y: Int): Int := x\n\
  fn argument(dummy: Int): Int := first(3, 1 div 0)\n\
  expect demand(b?: Bool) { assume a: b? or (1 div 0 = 0) expect e: let x := 1 div 0 in b? }\n\
  expect cycles(l: Light) { expect back: next(next(next(l))) = l }\n\
  expect waits(l: Light, base: Int) { assume bounded: base <= 100 expect at_most: wait(l, base) <= 130 }\n\
  expect wrong(l: Light) { expect never_red: next(l) != Light::Red }\n"

private def result (p : FrenThirDesugar.Program) (name : String) (member : Option String)
    (args : Array Value) (depth : Nat) : Outcome :=
  match evaluate (evaluator p) ⟨key name, member⟩ args depth with
  | .ok e => e.outcome
  | .error e => .error e

private def hasValue (o : Outcome) (v : Value) : Bool :=
  match o with | .ok actual => actual == v | _ => false
private def undefined (o : Outcome) : Bool :=
  match o with | .error (.undefined ..) => true | _ => false
private def invalid (o : Outcome) : Bool :=
  match o with | .error (.invalid ..) => true | _ => false
private def exhausted (o : Outcome) : Bool :=
  match o with | .error (.exhausted ..) => true | _ => false

private def sample (n : Nat) (x : Int) : Bool := Id.run do
  let .ok p := FrenThirDesugar.fromSource ⟨n⟩ source | return false
  let .ok actual := FrenHirToThir.checkWalkingSource ⟨n⟩ source | return false
  let q := desugar p
  if actual != q.typed then return false
  if q.typed != p.typed || q.typed.resolved.document.emit != source then return false
  if !hasValue (result q "wait" none #[light "Red", .int x] 100) (.int (x + 30)) then return false
  if !hasValue (result q "next" none #[light "Amber"] 100) (light "Red") then return false
  if !hasValue (result q "wrong" (some "never_red") #[light "Amber"] 100) (.bool false) then return false
  if !hasValue (result q "waits" (some "bounded") #[light "Red", .int x] 100) (.bool (x ≤ 100)) then return false
  -- Independent Language outcomes, beyond the identity theorem above.
  -- These exercise actual fromSource/desugar/evaluate, not a copied pass.
  let definedDemand := #[("unusedLet", none, #[Value.int x], Value.int 0),
    ("guarded", none, #[.int 0], .int 0), ("guarded", none, #[.int 1], .int 1),
    ("conjunction", none, #[.bool false], .bool false),
    ("disjunction", none, #[.bool true], .bool true),
    ("nested", none, #[.int x], .int 4), ("shadow", none, #[.int x], .int 8),
    ("capture", none, #[.int x], .int (x + 1)),
    ("demand", some "a", #[.bool true], .bool true),
    ("demand", some "e", #[.bool true], .bool true)]
  for (name, member, args, expected) in definedDemand do
    if !hasValue (result q name member args 100) expected then return false
  let undefinedDemand := #[("usedLet", none, #[Value.int x]),
    ("nestedUsed", none, #[.int x]), ("conjunction", none, #[.bool true]),
    ("disjunction", none, #[.bool false]), ("strictIff", none, #[.bool false]),
    ("strictIff", none, #[.bool true]), ("strictEq", none, #[.bool false]),
    ("strictEq", none, #[.bool true]), ("strictNe", none, #[.bool false]),
    ("strictNe", none, #[.bool true]), ("argument", none, #[.int x]),
    ("demand", some "a", #[.bool false])]
  for (name, member, args) in undefinedDemand do
    if !undefined (result q name member args 100) then return false
  if !hasValue (result q "demand" (some "e") #[.bool false] 100) (.bool false) then return false
  for (label, kind) in [("a", FrenAst.MemberKind.assume), ("e", .expect)] do
    let .ok e := evaluate (evaluator q) ⟨key "demand", some label⟩ #[.bool true] 100 | return false
    if e.body.member.map (·.kind) != some kind ||
        e.body.member.map (·.label.text) != some label ||
        (e.body.expression.tokens.head?).map (·.span.file) != some ⟨n⟩ then return false
  if !undefined (result q "partial" none #[.int x] 100) then return false
  if !invalid (result q "wait" none #[.bool true] 100) then return false
  if !exhausted (result q "wait" none #[light "Red", .int x] 0) then return false
  let bad := #["mod bad\nfn f(x: Int): Int := y + 1", "mod bad\nenum Light { Red, Green }\nfn f(l: Light): Int := l + 1", source ++ "\nfn loop(x: Int): Int := loop(x)", "mod bad\nfn f(x: Int): Int := ("]
  if bad.any (fun s => (FrenThirDesugar.fromSource ⟨n⟩ s).isOk) then return false
  if (FrenThirDesugar.fromResolved {p.input with references := #[]}).isOk then return false
  -- Independent controls distinguish omitted data from the retained value.
  if ({p.typed with bodies := #[]} : FrenModule.Typed) == q.typed then return false
  if ({p.typed with signatures := #[]} : FrenModule.Typed) == q.typed then return false
  if ({p.typed with resolved := {p.input with references := #[]}} : FrenModule.Typed) == q.typed then return false
  let .ok provenance := FrenThirDesugar.fromSource ⟨n + 1⟩ source | return false
  if provenance.typed == q.typed then return false
  let .ok members := FrenThirDesugar.fromSource ⟨n⟩ (source.replace "assume bounded:" "expect bounded:") | return false
  if members.typed == q.typed then return false
  let .ok noAssumption := FrenThirDesugar.fromSource ⟨n⟩ (source.replace "assume bounded: base <= 100 " "") | return false
  if noAssumption.typed == q.typed then return false
  let .ok noExpectation := FrenThirDesugar.fromSource ⟨n⟩ (source.replace "expect at_most: wait(l, base) <= 130" "") | return false
  if noExpectation.typed == q.typed then return false
  let .ok enumChange := FrenThirDesugar.fromSource ⟨n⟩ (source.replace "Amber" "Yellow") | return false
  if enumChange.typed == q.typed || hasValue (result enumChange "next" none #[light "Amber"] 100) (light "Red") then return false
  return true

private def checkProperty (p : Prop)
    (decorated : Decorations.DecorationsOf p := by mk_decorations) [Testable decorated] : IO Unit := do
  let report ← Testable.checkIO decorated {numInst := 100, maxSize := 35, randomSeed := some 20261112}
  IO.println s!"desugaring Plausible: {report}"
  match report with
  | .success _ => pure ()
  | _ => throw (IO.userError "desugaring property failed")

def run : IO Unit := do
  checkProperty <| ∀ (n : Nat) (x : Int), sample n x = true
  for n in [:24] do
    unless sample n (-(n : Int)) do throw (IO.userError s!"desugaring sample {n} failed")
  IO.println "desugaring census: 24 admitted, 96 rejected source, 24 rejected edited resolved, 312 undefined (13/sample), 24 each invalid/exhausted, 264 independent demand-defined (11/sample) and each witness/provenance/member/assumption/expectation/enum control; discarded=0"

#print axioms FrenThirDesugar.identity
#print axioms FrenThirDesugar.static
#print axioms FrenThirDesugar.admitted
#print axioms FrenThirDesugar.rejected
#print axioms FrenThirDesugar.deterministic
#print axioms evaluation

end FrenThirDesugarTests
