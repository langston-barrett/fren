module

public import FrenLirToOirTests.Controls
import Plausible

public section
namespace FrenLirToOirTests
open FrenOir FrenLir FrenEval Plausible
open scoped Plausible.Decorations

private def generated (k : Nat) : String :=
  "mod oir_walk\nfn ordinary(b?: Bool): Bool := b? and (1 div 0 = 0)\n" ++
  "fn unused(x: Int): Int := let dead := 1 div 0 in x\n" ++
  "fn shadow(x: Int): Int := let x := x + " ++ toString k ++ " in if x != 0 then 1 div x else 0\n" ++
  "expect safe(n: Int, d: Int) { expect goal: n div d = " ++ toString k ++
  " assume later: d != 0 }\nexpect empty() {}\n" ++
  "expect mutual(d: Int) { assume a: 1 div d = 0 assume b: 1 div d != 0 expect goal: false }\n" ++
  "expect contradictory() { assume no: false expect vacuous: false }"

/-- Each sample requires actual successful production, partial bodies,
contradiction and rejection controls. No implication or discarded premise. -/
private def sample (file n : Nat) : Bool := Id.run do
  let k := n % 19
  let src := generated k
  let .ok c := compile file src | return false
  let p := c.program
  if !graphAudit p || p.lir.mir.source != c.admitted.typed ||
      p.lir.mir.source.resolved.document.emit != src then return false
  let #[ordinary] := divisions p "ordinary" | return false
  let #[unused] := divisions p "unused" | return false
  if !ordinary.frames.isEmpty || !unused.frames.isEmpty ||
      !sees ordinary #[.bool false] true || !sees unused #[.int (k : Int)] true then return false
  let #[shadow] := divisions p "shadow" | return false
  match shadow.frames with
  | [.binding b .int _ _, .guard _ true] => if b.text != "x" then return false
  | _ => return false
  if !sees shadow #[.int (-(k : Int))] false then return false
  let some goal := one? p "safe" .validity (some "goal") | return false
  if goal.readiness != .ready ||
      goal.hypotheses.map (·.source.member.map (·.label.text)) != #[some "later"] ||
      !sees goal #[.int (k : Int), .int 1] false ||
      !sees goal #[.int ((k : Int) + 1), .int 1] true then return false
  let some empty := one? p "empty" .assumptionsSatisfiable | return false
  let some contradiction := one? p "contradictory" .assumptionsSatisfiable | return false
  if !sees empty #[] true || !sees contradiction #[] false then return false
  let mutualQuestions := owned p "mutual"
  if mutualQuestions.isEmpty || (divisions p "mutual").size != 2 || mutualQuestions.any (fun q => q.readiness == .ready) then
    return false
  let .ok again := compile file src | return false
  if again.program != p then return false
  let .ok shifted := compile (file + 1) src | return false
  if shifted.program == p then return false
  let flipped := {goal with condition := .unary .not goal.condition}
  if !sorted p flipped || !sees flipped #[.int (k : Int), .int 1] true then return false
  for invalid in #[src ++ "\nfn bad(x: Int): Int := false", src ++ "\nfn bad(x: Int): Int := absent",
      src ++ "\nfn loop(x: Int): Int := loop(x)"] do
    if (FrenLirToOir.fromSource ⟨file⟩ invalid).isOk then return false
  return true

private def property (p : Prop)
    (decorated : Decorations.DecorationsOf p := by mk_decorations) [Testable decorated] : IO Unit := do
  let report ← Testable.checkIO decorated {numInst := 100, maxSize := 35, randomSeed := some 20261121}
  IO.println s!"actual OIR Plausible: {report}"
  match report with
  | .success _ => pure ()
  | _ => throw (IO.userError "actual OIR source property failed")

def runProperties : IO Unit := do
  let started ← IO.monoMsNow
  property <| ∀ (file n : Nat), sample file n = true
  for n in [:19] do
    unless sample (700 + n) n do throw (IO.userError s!"OIR census sample {n}")
  IO.println s!"OIR properties execution: {(← IO.monoMsNow) - started} ms"
  IO.println "OIR census: 19 admitted sources, each with mandatory ordinary/unused partial bodies, safe single-partial goal, mutual-partial unresolved block, empty and contradictory blocks; 57 illtyped/unbound/recursive rejections, 19 independent polarity controls (generated omissions are not counted; fixed-fixture omission audit remains), 19 deterministic and 19 moved-file productions; Plausible 100 samples with same classes, discarded=0. Finite observations are not solver results or universal soundness."

#print axioms FrenLirToOir.deterministic
#print axioms FrenLirToOir.retains_lir
#print axioms FrenLirToOir.retained_equations
#print axioms FrenLirToOir.admission
#print axioms FrenLirToOir.retains_source
#print axioms FrenLirToOir.scoped_input
#print axioms FrenLirToOir.lowering_rejected
#print axioms FrenLirToOir.walk_both
#print axioms FrenLirToOir.walk_check
#print axioms FrenLirToOir.walk_empty
#print axioms FrenLirToOir.walk_at
#print axioms FrenLirToOir.walk_binding
#print axioms FrenLirToOir.walk_branch

end FrenLirToOirTests
