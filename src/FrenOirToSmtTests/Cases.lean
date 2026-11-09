module

public import FrenOirToSmtTests.Support

public section
namespace FrenOirToSmtTests
open FrenOirToSmt

def source : String := "mod smt_walk\n\
  enum A { One, Two }\n\
  enum B { One, Two }\n\
  fn forward(x: Int): Int := later(x)\n\
  fn later(x: Int): Int := x + 1\n\
  fn unused(x: Int): Int := let dead := 1 div 0 in 0\n\
  fn guarded(d: Int): Int := if d != 0 then 1 div d else 0\n\
  fn shadow(x: Int): Int := let x := x + 1 in let x := x + 2 in x\n\
  fn choose(a: A): Int := match a { A::One => 3, A::Two => 7 }\n\
  fn falseBranch(x: Int): Int := if false then 1 div 0 else 0\n\
  expect truths() { expect good: true expect bad: false }\n\
  expect empty() {}\n\
  expect contradictory() { assume never: false expect vacuous: false }\n\
  expect arithmetic() { expect negativeDividend: (-9) div 2 = -5\n\
    expect negativeDivisor: (-9) div (-2) = 5 expect negativeRemainder: (-9) % (-2) = 1\n\
    expect positiveDividend: 9 div (-2) = -4 expect positiveRemainder: 9 % (-2) = 1\n\
    expect operators: (1 < 2) and (1 <= 1) and (2 > 1) and (2 >= 2) and (1 != 2)\n\
    expect booleans: (true iff false) = false expect sum: 1 + 2 * 3 - 4 = 3 }\n\
  expect safe(n: Int, d: Int) { assume nonzero: d != 0 expect reflexive: n div d = n div d }\n\
  expect partials() { expect andGoal: false and (1 div 0 = 0)\n\
    expect orGoal: true or (1 div 0 = 0) expect letGoal: let x := 1 div 0 in true }\n\
  expect calls(x: Int) { expect forward: forward(x) = x + 1 expect shadow: shadow(x) = x + 3 }\n\
  expect nominal(a: A, b: B) { expect range: choose(a) = 3 or choose(a) = 7\n\
    expect each: a = A::One or a = A::Two expect other: b = B::One or b = B::Two }\n\
  expect mutual(d: Int) { assume a: 1 div d = 0 assume b: 1 div d != 0 expect goal: false }\n\
  expect late(n: Int, d: Int) { expect goal: n div d = 0 assume nonzero: d != 0 }\n"

/-- This census is independent of the translator: it specifies every written
validity and Sat request from this source, with separate domain expectations. -/
def audit (p : Program) (rs : Array Result) : IO Unit := do
  require (p.queries.size == p.oir.questions.size && rs.size == p.queries.size) "question retention"
  for i in [:rs.size] do
    let some r := rs[i]? | throw (IO.userError "result index")
    let some original := p.oir.questions[i]? | throw (IO.userError "OIR index")
    require (r.query.question == original) "original IDs/attribution/dependencies/readiness"
    require (r.outcome == .sat || r.outcome == .unsat) s!"unexpected nonanswer: {reprStr r}"
    let some receipt := r.receipt | throw (IO.userError "missing actual solver receipt")
    require (receipt.exitCode == some 0 && receipt.command.size == 4) "actual cvc5 invocation"
  let inventory := rs.filterMap fun r => match r.query.question.kind with
    | .validity => some (name r, label r)
    | .assumptionsSatisfiable => some (name r, "sat")
    | _ => none
  require (inventory == #[("truths", "sat"), ("truths", "good"), ("truths", "bad"), ("empty", "sat"),
    ("contradictory", "sat"), ("contradictory", "vacuous"), ("arithmetic", "sat"),
    ("arithmetic", "negativeDividend"), ("arithmetic", "negativeDivisor"), ("arithmetic", "negativeRemainder"),
    ("arithmetic", "positiveDividend"), ("arithmetic", "positiveRemainder"), ("arithmetic", "operators"),
    ("arithmetic", "booleans"), ("arithmetic", "sum"), ("safe", "sat"), ("safe", "reflexive"),
    ("partials", "sat"), ("partials", "andGoal"), ("partials", "orGoal"), ("partials", "letGoal"),
    ("calls", "sat"), ("calls", "forward"), ("calls", "shadow"), ("nominal", "sat"),
    ("nominal", "range"), ("nominal", "each"), ("nominal", "other"), ("mutual", "sat"),
    ("mutual", "goal"), ("late", "sat"), ("late", "goal")]) "independent written request inventory"
  for r in rs do
    if r.query.question.kind == .assumptionsSatisfiable then
      let expected := if ["contradictory", "mutual"].contains (name r) then Outcome.unsat else .sat
      require (r.outcome == expected) s!"Sat polarity {name r}"
    if r.query.question.kind == .validity then
      let expected := if (name r == "truths" && label r == "bad") ||
          (name r == "partials" && label r == "andGoal") || name r == "late" then Outcome.sat else .unsat
      require (r.outcome == expected) s!"validity polarity {name r}/{label r}"
    if name r == "mutual" then
      require (r.query.question.readiness != .ready) "unresolved partial dependencies lost"
    if isDomain r && name r != "mutual" then
      let expected := if isNonzero r && ["unused", "partials"].contains (name r) then Outcome.sat else .unsat
      require (r.outcome == expected) s!"domain search {name r}/{label r}: {reprStr r.outcome}"
  for owner in ["unused", "guarded", "falseBranch"] do
    let domains := rs.filter (fun r => name r == owner && isNonzero r)
    require (domains.size == 1) s!"retained unused/guarded definition {owner}"
  require ((rs.filter (fun r => name r == "partials" && isNonzero r)).size == 3)
    "both Boolean operands and unused lets have static domain questions"

def runCases : IO Unit := do
  let started ← IO.monoMsNow
  let (p, rs) ← results source
  audit p rs
  for r in rs do
    let script := r.query.script.toOption.getD "translation failed"
    evidence "native" (Lean.Json.mkObj [("question_id", Lean.toJson r.query.question.id),
      ("owner", Lean.toJson (reprStr r.query.question.owner)),
      ("origin", Lean.toJson (reprStr r.query.question.origin)),
      ("parameters", Lean.toJson (reprStr r.query.question.parameters)),
      ("dependencies", Lean.toJson (reprStr r.query.question.dependencies)),
      ("readiness", Lean.toJson (reprStr r.query.question.readiness)),
      ("kind", Lean.toJson (reprStr r.query.question.kind)), ("script", Lean.toJson script),
      ("receipt", r.receipt.map receiptJson |>.getD Lean.Json.null)])
  IO.println s!"SMT producer execution: {(← IO.monoMsNow) - started} ms; {rs.size} real cvc5 answers, 32 independently expected requests, 7 actual definitions, 2 nominal enums; raw evidence only, mutual readiness unresolved"

end FrenOirToSmtTests
