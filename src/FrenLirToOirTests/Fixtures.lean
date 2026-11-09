module

public import FrenLirToOirTests.Support

public section
namespace FrenLirToOirTests
open FrenOir FrenLir FrenEval

def source : String := "mod oir_walk\n\
  enum Light { Red, Green }\n\
  enum Other { Red, Green }\n\
  fn constant(dummy: Int): Int := 0\n\
  fn unused(dummy: Int): Int := let dead := 1 div 0 in 0\n\
  fn preGuard(d: Int): Int := let x := 1 div d in if d != 0 then x else 0\n\
  fn nested(x: Int): Int := let x := x + 1 in let x := x + 2 in if x != 0 then 1 div x else 0\n\
  fn calls(d: Int): Int := constant(1 div d)\n\
  fn selected(l: Light): Int := match l { Light::Red => 1 div 0, Light::Green => 2 div 0 }\n\
  fn andCheck(b?: Bool): Bool := b? and (1 div 0 = 0)\n\
  fn orCheck(b?: Bool): Bool := b? or (1 div 0 = 0)\n\
  fn falseAnd(dummy: Int): Bool := false and (1 div 0 = 0)\n\
  fn trueOr(dummy: Int): Bool := true or (1 div 0 = 0)\n\
  fn falseBranch(dummy: Int): Int := if false then 1 div 0 else 0\n\
  fn nonzeroGuard(d: Int): Int := if d != 0 then 1 div d else 0\n\
  expect safe(n: Int, d: Int) { expect goal: n div d = 0 assume nonzero: d != 0 }\n\
  expect mutual(d: Int) { assume a: 1 div d = 0 assume b: 1 div d != 0 expect goal: false }\n\
  expect contradictory() { expect vacuous: false assume no: false }\n\
  expect empty() {}\n\
  expect own(d: Int) { assume yes: true expect goal: d = 0 }\n\
  expect same() { expect a: 1 div 0 = 0 expect b: 1 div 0 = 0 }\n\
  expect nominal(l: Light, o: Other, b?: Bool, n: Int) { expect goal: b? or n = 0 }\n"

def light (name : String) : Value := .enum (key "Light") ((key "Light").named name)

/-- Independent source census and selected mathematical counterexamples. This
never compares the output with a second invocation of the extraction helper. -/
def sourceAudit (p : FrenOir.Program) : Bool := Id.run do
  if !graphAudit p || p.definitions.map (·.signature.id) !=
      #["constant", "unused", "preGuard", "nested", "calls", "selected", "andCheck", "orCheck",
        "falseAnd", "trueOr", "falseBranch", "nonzeroGuard"].map key then return false
  if p.enumerations.map (·.id) != #[key "Light", key "Other"] then return false
  let inventory := p.questions.filterMap fun q => match q.kind with
    | .assumptionsSatisfiable => some (q.owner, "sat")
    | .validity => some (q.owner, (label q).getD "missing")
    | _ => none
  if inventory != #[(key "safe", "sat"), (key "safe", "goal"), (key "mutual", "sat"),
      (key "mutual", "goal"), (key "contradictory", "sat"), (key "contradictory", "vacuous"),
      (key "empty", "sat"), (key "own", "sat"), (key "own", "goal"),
      (key "same", "sat"), (key "same", "a"), (key "same", "b"),
      (key "nominal", "sat"), (key "nominal", "goal")] then return false
  for name in ["unused", "preGuard", "andCheck", "orCheck", "falseAnd", "trueOr"] do
    let #[q] := divisions p name | return false
    if !q.frames.isEmpty || !q.hypotheses.isEmpty || q.kind != .functionDefinedness ||
        q.request.isSome || q.readiness != .ready then return false
    let some origin := q.origin | return false
    match origin.expression with
    | .binary _ token .div _ => if token.text != "div" then return false
    | _ => return false
    let arg := if name == "andCheck" then Value.bool false else
      if name == "orCheck" then Value.bool true else Value.int 0
    if !sees q #[arg] true then return false
  let #[f] := divisions p "falseBranch" | return false
  match f.frames with
  | [.guard c true] => if strip 50 c != .bool false || !sees f #[.int 0] false then return false
  | _ => return false
  let #[g] := divisions p "nonzeroGuard" | return false
  match g.frames with
  | [.guard _ true] =>
    if !sees g #[.int 0] false || !sees g #[.int 1] false || g.dependencies.isEmpty then return false
  | _ => return false
  let #[nested] := divisions p "nested" | return false
  match nested.frames with
  | [.binding a .int _ _, .binding b .int _ _, .guard _ true] =>
    if a.text != "x" || b.text != "x" || a == b then return false
  | _ => return false
  if nested.origin.map (·.context.map (·.1.text)) != some ["x", "x", "x"] ||
      !sees nested #[.int (-3)] false || !sees nested #[.int (-1)] false then return false
  let #[red, green] := divisions p "selected" | return false
  match red.frames, green.frames with
  | [.guard a true], [.guard b false] =>
    if a != b then return false
    match strip 100 a with
    | .binary .eq _ (.constructor owner ctor) =>
      if owner != key "Light" || ctor != (key "Light").named "Red" then return false
    | _ => return false
  | _, _ => return false
  if !sees red #[light "Red"] true || !sees red #[light "Green"] false ||
      !sees green #[light "Green"] true || !sees green #[light "Red"] false then return false
  let calls := owned p "calls"
  let #[call] := calls.filter (fun q => match q.condition with | .app _ .domain _ => true | _ => false)
    | return false
  if !call.dependencies.contains (.definition (key "constant")) then return false
  let some constant := p.definitions.find? (fun d => d.signature.id == key "constant") | return false
  if strip 20 constant.value != .int 0 || strip 20 constant.domain != .bool true then return false
  let some nominal := one? p "nominal" .assumptionsSatisfiable | return false
  if nominal.parameters.map (·.source.written.name.text) != #["l", "o", "b?", "n"] ||
      nominal.context.map (·.1.text) != ["n", "b?", "o", "l"] ||
      nominal.parameters.map (·.domain) != #[
        .enumeration (key "Light") #[(key "Light").named "Red", (key "Light").named "Green"],
        .enumeration (key "Other") #[(key "Other").named "Red", (key "Other").named "Green"],
        .boolean, .integer] then return false
  return true

end FrenLirToOirTests
