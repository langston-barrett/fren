module

public import FrenFlatToLirTests.Verification
import Plausible

public section
namespace FrenFlatToLirTests
open FrenLir FrenEval Plausible
open scoped Plausible.Decorations

private def generated (n : Nat) : String :=
  "mod lir_walk\nfn add(x: Int): Int := let y := x + " ++ toString n ++ " in y + y\n" ++
  "fn guard(d: Int): Int := if d != 0 then let x := 1 div d in x else 0\n" ++
  "expect checks(x: Int) { expect first: x <= " ++ toString n ++
  " assume later: x <= " ++ toString n ++ " }\nexpect empty() {}\n" ++
  "fn andCheck(b?: Bool): Bool := b? and (1 div 0 = 0)\n" ++
  "fn orCheck(b?: Bool): Bool := b? or (1 div 0 = 0)\n" ++
  "fn unusedCheck(x: Int): Int := let bad := 1 div 0 in x\n" ++
  "fn scoped(d: Int): Int := let d := d + 1 in if d != 0 then 1 div d else 0"

/-- Direct Plausible over the real admitted-source producer. Each sample has
valid, partial and invalid classes, with no implication/discarded premises.
The expected arithmetic and request inventory are written independently. -/
private def sample (file n : Nat) : Bool := Id.run do
  let k := n % 31
  let source := generated k
  let .ok c := compile file source | return false
  if !c.program.wellFormed || c.program.mir.source != c.admitted.typed ||
      c.program.mir.source.resolved.document.emit != source then return false
  if !agrees c "add" #[.int (-(k : Int))] (some (.int 0)) ||
      !agrees c "add" #[.int 3] (some (.int (2 * (3 + (k : Int))))) ||
      !agrees c "guard" #[.int 0] (some (.int 0)) ||
      !agrees c "guard" #[.int 1] (some (.int 1)) then return false
  if c.program.requests.map (fun r => (r.source.owner, labels r.assumptions, labels r.demand)) !=
      #[(key "checks", #["later"], #["later"]),
        (key "checks", #["later"], #["later", "first"]), (key "empty", #[], #[])] then return false
  if !agrees c "checks" #[.int (k : Int)] (some (.bool true)) (some "first") ||
      !agrees c "checks" #[.int ((k : Int) + 1)] (some (.bool false)) (some "first") then return false
  -- Mandatory old-semantics counterexamples: no evaluation trace oracle.
  if !domainIs c "andCheck" #[.bool false] false ||
      !domainIs c "orCheck" #[.bool true] false ||
      !domainIs c "unusedCheck" #[.int (k : Int)] false ||
      !agrees c "scoped" #[.int (-1)] (some (.int 0)) then return false
  for name in ["andCheck", "orCheck", "unusedCheck"] do
    let some b := body? c.program name | return false
    let [leaf] := nonzeroLeaves b | return false
    if !leaf.guards.isEmpty || !leaf.binders.isEmpty || leaf.origin.isNone then return false
  let some scopedBody := body? c.program "scoped" | return false
  let [leaf] := nonzeroLeaves scopedBody | return false
  if leaf.guards.map Prod.snd != [true] || leaf.binders.map (·.1.text) != ["d"] then return false
  let some origin := leaf.origin | return false
  if origin.context.map (·.1.text) != ["d", "d"] then return false
  let .ok again := compile file source | return false
  if c.program != again.program then return false
  let .ok moved := compile (file + 1) source | return false
  if c.program.mir.source == moved.program.mir.source then return false
  let .ok mutant := compile file (source.replace s!"x + {k}" s!"x + {k + 1}") | return false
  if agrees mutant "add" #[.int 3] (some (.int (2 * (3 + (k : Int))))) then return false
  let partialSource := "mod lir_walk\nexpect partial(x: Int) { expect goal: x div 0 = 0 assume later: x <= 10 }"
  let .ok p := compile file partialSource | return false
  if p.program.requests.size != 2 ||
      !agrees p "partial" #[.int (k : Int)] none (some "goal") then return false
  for text in #[source ++ "\nfn loop(x: Int): Int := loop(x)", source ++ "\nfn bad(x: Int): Int := false",
      source ++ "\nfn bad(x: Int): Int := absent", source ++ "\nfn bad(x: Int): Int := ("] do
    if (FrenFlatToLir.fromSource ⟨file⟩ text).isOk then return false
  if (FrenWalking.fromResolved {c.admitted.input with references := #[]}).isOk then return false
  return true

private def property (p : Prop)
    (decorated : Decorations.DecorationsOf p := by mk_decorations) [Testable decorated] : IO Unit := do
  let report ← Testable.checkIO decorated {numInst := 100, maxSize := 35, randomSeed := some 20261120}
  IO.println s!"actual LIR Plausible: {report}"
  match report with
  | .success _ => pure ()
  | _ => throw (IO.userError "actual LIR source property failed")

def runProperties : IO Unit := do
  let started ← IO.monoMsNow
  property <| ∀ (file n : Nat), sample file n = true
  for n in [:24] do
    unless sample (400 + n) n do throw (IO.userError s!"LIR census sample {n} failed")
  IO.println s!"LIR properties execution: {(← IO.monoMsNow) - started} ms"
  IO.println "LIR census: 24 valid base + 24 partial sources, 96 rejected sources + 24 edited-resolution rejections, 24 admitted arithmetic mutants killed; 72 base + 48 partial requests, 96 false verification domains + 24 guarded/scoped obligation trees. Plausible: 100 samples, same mandatory classes; discarded=0, 7 value comparisons/sample require true verification domains; false domains checked without the evaluator; all admission premises witnessed by actual producer."

#print axioms FrenFlatToLir.retains_mir
#print axioms FrenFlatToLir.retains_source
#print axioms FrenFlatToLir.declaration_retention_check
#print axioms FrenFlatToLir.request_retention_check
#print axioms FrenFlatToLir.admission
#print axioms FrenFlatToLir.wellFormed
#print axioms FrenFlatToLir.deterministic
#print axioms FrenFlatToLir.rejected
#print axioms FrenLir.branch_domain
#print axioms FrenLir.bind_domain
#print axioms FrenLir.strict_domain
#print axioms FrenLir.call_domain
#print axioms FrenLir.binary_verification
#print axioms FrenLir.bind_verification

end FrenFlatToLirTests
