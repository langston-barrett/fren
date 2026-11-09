module

public import FrenOirToSmtTests.Controls
import Plausible

public section
namespace FrenOirToSmtTests
open FrenOirToSmt Plausible
open scoped Plausible.Decorations

private def generated (k : Nat) : String :=
  "mod generated\nfn unused(x: Int): Int := let bad := 1 div 0 in x\n" ++
  "expect checks(n: Int, d: Int) { expect goal: n div d = " ++ toString k ++
  " assume later: d != 0 }\nexpect empty() {}"

private def sample (file n : Nat) : Bool := Id.run do
  let k := n % 17
  let text := generated k
  let .ok p := FrenThirDesugar.fromSource ⟨file⟩ text | return false
  let .ok out := produce p | return false
  if out.oir.lir.mir.source != p.typed || out.queries.size != out.oir.questions.size ||
      out.queries.any (fun q => !q.script.isOk) then return false
  let inventory := out.queries.filterMap (fun q => match q.question.kind with
    | .assumptionsSatisfiable => some "sat"
    | .validity => some "goal"
    | _ => none)
  if inventory != #["sat", "goal", "sat"] then return false
  let partials := out.queries.filter (fun q => q.question.kind == .functionDefinedness &&
    (match q.question.condition with | .binary .ne _ (.int 0) => true | _ => false))
  if partials.size != 1 || partials.any (fun q => !q.question.frames.isEmpty) then return false
  let .ok again := produce p | return false
  if out.queries.map (·.script.toOption) != again.queries.map (·.script.toOption) then return false
  let .ok moved := FrenOirToSmt.fromSource ⟨file + 1⟩ text | return false
  if out.queries.map (·.script.toOption) != moved.queries.map (·.script.toOption) then return false
  if out.oir.lir.mir.source == moved.oir.lir.mir.source then return false
  for invalid in #[text ++ "\nfn bad(x: Int): Int := false", text ++ "\nfn loop(x: Int): Int := loop(x)"] do
    if (FrenOirToSmt.fromSource ⟨file⟩ invalid).isOk then return false
  let i := n % 200
  let symbols := #[Symbol.sort i, .constructor i 0, .constructor i 1, .function i .value,
    .function i .domain, .parameter i, .local i .value, .local i .domain]
  if symbols.toList.eraseDups.length != 8 || (symbols.map Symbol.render).toList.eraseDups.length != 8 then
    return false
  return true

private def property (p : Prop)
    (decorated : Decorations.DecorationsOf p := by mk_decorations) [Testable decorated] : IO Unit := do
  let report ← Testable.checkIO decorated {numInst := 100, maxSize := 35, randomSeed := some 20261122}
  IO.println s!"actual SMT translation Plausible: {report}"
  match report with
  | .success _ => pure ()
  | _ => throw (IO.userError "actual SMT source property")

def runProperties : IO Unit := do
  let started ← IO.monoMsNow
  property <| ∀ (file n : Nat), sample file n = true
  for n in [:17] do
    require (sample (900 + n) n) "translation source census"
  -- Real solver checks are separate from pure Plausible. Each pair has an
  -- independently specified constant equality and an admitted false mutant.
  for n in [:7] do
    for (offset, expected) in [(1, Outcome.unsat), (2, .sat)] do
      let text := s!"mod generated\nexpect checks() \{ expect goal: {n} + 1 = {n + offset} }"
      let (_, rs) ← results text
      answer rs "checks" "goal" expected
  IO.println s!"SMT properties execution: {(← IO.monoMsNow) - started} ms; 100 Plausible samples, discarded=0; census 17 admitted/partial sources + 34 rejected + 17 moved-file/determinism; 14 actual cvc5 source equality/mutant cases"

#print axioms FrenOirToSmt.deterministic
#print axioms FrenOirToSmt.retains_oir
#print axioms FrenOirToSmt.retains_questions
#print axioms FrenOirToSmt.admission
#print axioms FrenOirToSmt.distinct_components
#print axioms FrenOirToSmt.parameter_domain
#print axioms FrenOirToSmt.classify_nonzero
#print axioms FrenOirToSmt.classify_resource

end FrenOirToSmtTests
