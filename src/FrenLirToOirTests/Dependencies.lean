module

public import FrenLirToOirTests.Fixtures

public section
namespace FrenLirToOirTests
open FrenOir FrenLir FrenEval

def dependencyAudit (p : FrenOir.Program) : Bool := Id.run do
  let safe := owned p "safe"
  if safe.any (fun q => q.readiness != .ready) then return false
  let assumed := safe.filter (fun q => q.kind == .assumptionDefinedness)
  if assumed.isEmpty || assumed.any (fun q => !q.hypotheses.isEmpty) then return false
  let #[domain] := divisions p "safe" | return false
  if domain.hypotheses.map (·.source.member.map (·.label.text)) != #[some "nonzero"] ||
      !sees domain #[.int 1, .int 0] false || !sees domain #[.int 1, .int 1] false then return false
  let some valid := one? p "safe" .validity (some "goal") | return false
  let some sat := one? p "safe" .assumptionsSatisfiable | return false
  if !sees valid #[.int 1, .int 1] true || !sees valid #[.int 0, .int 1] false ||
      !sees valid #[.int 1, .int 0] false || !sees sat #[.int 1, .int 0] false ||
      !sees sat #[.int 0, .int 1] true then return false
  for q in safe do
    if q.kind == .goalDefinedness || q.kind == .assumptionDefinedness then
      if !valid.dependencies.contains (.question q.id) then return false
    if q.kind == .assumptionDefinedness && !sat.dependencies.contains (.question q.id) then return false
  let mutualQuestions := owned p "mutual"
  let partials := mutualQuestions.filter (fun q => q.kind == .assumptionDefinedness)
  if (divisions p "mutual").size != 2 || partials.size != 4 ||
      mutualQuestions.any (fun q => q.readiness == .ready) then return false
  for q in partials do
    let expected := if label q == some "a" then "b" else "a"
    if q.hypotheses.map (·.source.member.map (·.label.text)) != #[some expected] then return false
    let siblings := partials.filter (fun r => label r == some expected)
    if !siblings.all (fun r => q.dependencies.contains (.question r.id)) then return false
  let some empty := one? p "empty" .assumptionsSatisfiable | return false
  if empty.search != .bool true || !empty.parameters.isEmpty || !empty.dependencies.isEmpty then return false
  let some contradictory := one? p "contradictory" .assumptionsSatisfiable | return false
  let some vacuous := one? p "contradictory" .validity (some "vacuous") | return false
  if !sees contradictory #[] false || !sees vacuous #[] false ||
      contradictory.interpret .unsat != .unsatisfiableAssumptionSearch ||
      vacuous.interpret .unsat != .noCounterexample then return false
  for q in owned p "own" do
    if q.hypotheses.any (fun b => b.source.owner != key "own") || q.readiness != .ready then return false
  let #[first, second] := divisions p "same" | return false
  if first.origin == second.origin || first.id == second.id ||
      label first != some "a" || label second != some "b" then return false
  -- No unproved goal is used as a hypothesis in any question.
  if p.questions.any (fun q => q.hypotheses.any (fun b =>
      b.source.member.any (·.kind != .assume))) then return false
  return true

def runCases : IO Unit := do
  let start ← IO.monoMsNow
  let c ← load source
  require (sourceAudit c.program) "independent source census/scopes/guards/formulas"
  require (dependencyAudit c.program) "assumption dependencies, ownership and polarity"
  let .ok again := compile 601 source | throw (IO.userError "determinism production")
  require (c.program == again.program) "deterministic actual production"
  require (c.program.lir.mir.source == c.admitted.typed) "retained admission witness"
  let .ok order := compile 602 "mod oir_walk\nexpect first() {}\nfn later(x: Int): Int := 1 div 0\nexpect last() {}"
    | throw (IO.userError "interleaved declarations")
  require (order.program.questions.map (·.owner) == #[key "first", key "later", key "last"])
    "declaration order across definitions and requests"
  IO.println s!"OIR producer execution: {(← IO.monoMsNow) - start} ms; {c.program.questions.size} questions, 12 retained definitions, 2 nominal enums, 14 ordered requests; safe single-partial and unresolved mutual-partial assumptions; no solver run"

end FrenLirToOirTests
