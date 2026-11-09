module

public import FrenFlatToLirTests.Probe

public section
namespace FrenFlatToLirTests
open FrenLir FrenEval

/-- The chapter's walking declarations, including the later assumption.
The Fren1 #fren_check fence directive is not part of Fren2 source syntax. -/
def walkingSource : String := "pub mod lir_walk\n\
  pub enum Light { Red, Green }\n\
  pub fn wait(l: Light, base: Int): Int := match l {\n\
    Light::Red => base + 30, Light::Green => base, }\n\
  expect waits(l: Light, base: Int) {\n\
    expect limit: wait(l, base) <= 130\n\
    assume bounded: base <= 100 }\n"

def demandSource : String := "mod lir_walk\n\
  enum Light { Red, Green }\n\
  enum Other { Red, Green }\n\
  fn ignore(x: Int): Int := 0\n\
  fn unused(dummy: Int): Int := let x := 1 div 0 in 0\n\
  fn guarded(d: Int): Int := let x := 1 div 0 in if d != 0 then x else 0\n\
  fn conditional(b?: Bool): Int := if b? then 1 div 0 else 0\n\
  fn constantBranch(dummy: Int): Int := if false then 1 div 0 else 0\n\
  fn bothGood(b?: Bool): Bool := b? and (2 = 2)\n\
  fn divide(n: Int, d: Int): Int := if d != 0 then n div d else 0\n\
  fn remainder(n: Int, d: Int): Int := if d != 0 then n mod d else 0\n\
  fn lazyAnd(b?: Bool): Bool := b? and (1 div 0 = 0)\n\
  fn lazyOr(b?: Bool): Bool := b? or (1 div 0 = 0)\n\
  fn strictIff(b?: Bool): Bool := b? iff (1 div 0 = 0)\n\
  fn strictEq(b?: Bool): Bool := b? = (1 div 0 = 0)\n\
  fn strictNe(b?: Bool): Bool := b? != (1 div 0 = 0)\n\
  fn reflexive(dummy: Int): Bool := (1 div 0) = (1 div 0)\n\
  fn strictAdd(dummy: Int): Int := 0 + (1 div 0)\n\
  fn strictCall(dummy: Int): Int := ignore(1 div 0)\n\
  fn safeCall(d: Int): Int := if d = 0 then 0 else ignore(1 div 0)\n\
  fn selected(l: Light): Int := match l { Light::Red => 1 div 0, Light::Green => 0 }\n\
  fn shadow(x: Int): Int := let x := x + 1 in let x := x + 2 in x + x\n\
  fn skipped(dummy: Int): Int := let x := 1 div 0 in let x := 7 in x + x\n\
  expect demand(b?: Bool) {\n\
    expect goal: let x := 1 div 0 in b?\n\
    expect strict: false iff (1 div 0 = 0)\n\
    assume later: b? or (1 div 0 = 0) }\n\
  expect other(x: Int) { assume own: x > 20 expect goal: x > 10 }\n\
  expect vacuous() { expect no: false assume contradiction: false }\n\
  expect empty() {}\n"

def labels (bs : Array Body) : Array String :=
  bs.map fun b => b.source.member.map (·.label.text) |>.getD "definition"

/-- Fixed external expectations for every request, not just a comparison with
MIR's request builder. Sat is distinct from validity; demands are roots. -/
def requestAudit (p : FrenLir.Program) : Bool :=
  p.requests.map (fun r => (r.source.owner, labels r.assumptions,
    (match r.question with
      | .assumptionsSatisfiable => "sat"
      | .validity b => b.source.member.map (·.label.text) |>.getD "missing"), labels r.demand,
    r.source.parameters.map (·.written.name.text), r.source.context.map (·.1.text))) == #[
    (key "demand", #["later"], "sat", #["later"], #["b?"], ["b?"]),
    (key "demand", #["later"], "goal", #["later", "goal"], #["b?"], ["b?"]),
    (key "demand", #["later"], "strict", #["later", "strict"], #["b?"], ["b?"]),
    (key "other", #["own"], "sat", #["own"], #["x"], ["x"]),
    (key "other", #["own"], "goal", #["own", "goal"], #["x"], ["x"]),
    (key "vacuous", #["contradiction"], "sat", #["contradiction"], #[], []),
    (key "vacuous", #["contradiction"], "no", #["contradiction", "no"], #[], []),
    (key "empty", #[], "sat", #[], #[], [])]

/-- Static domains are independent expectations. Value comparisons are used
only in true-domain cases; lazy interpreter outcomes do not decide checks. -/
def demandAudit (c : Compiled) : Bool :=
  requestAudit c.program && c.program.wellFormed &&
  domainIs c "unused" #[.int 0] false &&
  domainIs c "guarded" #[.int 0] false &&
  agrees c "guarded" #[.int 1] none &&
  agrees c "conditional" #[.bool false] (some (.int 0)) &&
  domainIs c "conditional" #[.bool true] false &&
  agrees c "constantBranch" #[.int 0] (some (.int 0)) &&
  agrees c "bothGood" #[.bool false] (some (.bool false)) &&
  agrees c "divide" #[.int 9, .int 0] (some (.int 0)) &&
  agrees c "divide" #[.int (-9), .int 2] (some (.int (-5))) &&
  agrees c "remainder" #[.int (-9), .int (-2)] (some (.int 1)) &&
  domainIs c "lazyAnd" #[.bool false] false &&
  domainIs c "lazyOr" #[.bool true] false &&
  agrees c "lazyAnd" #[.bool true] none && agrees c "lazyOr" #[.bool false] none &&
  agrees c "strictIff" #[.bool false] none && agrees c "strictEq" #[.bool false] none &&
  agrees c "strictNe" #[.bool true] none && agrees c "reflexive" #[.int 0] none &&
  agrees c "strictAdd" #[.int 0] none && agrees c "strictCall" #[.int 0] none &&
  agrees c "safeCall" #[.int 0] (some (.int 0)) && agrees c "safeCall" #[.int 1] none &&
  agrees c "selected" #[light "Green"] (some (.int 0)) &&
  agrees c "selected" #[light "Red"] none &&
  agrees c "shadow" #[.int 4] (some (.int 14)) &&
  domainIs c "skipped" #[.int 0] false &&
  domainIs c "demand" #[.bool false] false (some "goal") &&
  domainIs c "demand" #[.bool true] false (some "later") &&
  agrees c "demand" #[.bool false] none (some "later") &&
  agrees c "demand" #[.bool true] none (some "strict") &&
  agrees c "vacuous" #[] (some (.bool false)) (some "no") &&
  agrees c "vacuous" #[] (some (.bool false)) (some "contradiction")

end FrenFlatToLirTests
