module

public import FrenThirToMir
public import FrenEval

public section
namespace FrenThirToMirTests
open FrenMir FrenModule

def require (b : Bool) (why : String) : IO Unit :=
  unless b do throw (IO.userError why)

def key (s : String) : FrenBase.ItemId := FrenBase.ItemId.root.named "skeleton" |>.named s

def light (s : String) : FrenEval.Value := .enum (key "Light") ((key "Light").named s)

structure Compiled where
  admitted : FrenWalking.Program
  theory : Theory
  produced : FrenThirToMir.produce admitted = .ok theory

def compile (file : Nat) (source : String) : Except String Compiled := do
  let p ← (FrenWalking.fromSource ⟨file⟩ source).mapError (fun e => s!"admission: {repr e}")
  match h : FrenThirToMir.produce p with
  | .error e => .error s!"producer: {repr e}"
  | .ok t => .ok ⟨p, t, h⟩

def load (source : String) : IO Compiled :=
  match compile 101 source with
  | .ok c => pure c
  | .error e => throw (IO.userError e)

/-- Evaluate the producer's retained source, using its admission law. This is
only a concrete probe; request preservation is checked independently below. -/
def evaluator (c : Compiled) : FrenEval.Program :=
  ⟨c.admitted.input, c.theory.source, FrenThirToMir.admission _ _ c.produced⟩

def outcome (c : Compiled) (owner : String) (args : Array FrenEval.Value)
    (label : Option String := none) (depth : Nat := 100) : FrenEval.Outcome :=
  match FrenEval.evaluate (evaluator c) ⟨key owner, label⟩ args depth with
  | .error e => .error e
  | .ok e => e.outcome

def value (o : FrenEval.Outcome) (v : FrenEval.Value) : Bool :=
  match o with | .ok actual => actual == v | _ => false

def labels (bodies : Array TypedBody) : Array String :=
  bodies.map fun b => b.member.map (·.label.text) |>.getD "<definition>"

def slots (ctx : TypeContext) : List String := ctx.map (·.1.text)

def block (t : Theory) (name : String) : Option Block :=
  t.declarations.findSome? fun d => match d with
    | .block b => if b.owner == key name then some b else none
    | _ => none

def function (t : Theory) (name : String) : Option FrenMir.Function :=
  t.declarations.findSome? fun d => match d with
    | .function f => if f.signature.id == key name then some f else none
    | _ => none

def declarationIds (t : Theory) : Array FrenBase.ItemId :=
  t.declarations.map fun d => match d with
    | .enumeration e => e.id
    | .function f => f.signature.id
    | .block b => b.owner

/-- Raw request expectations: identities, role selection, full later assumption
sets, parameter order and nearest-first context. No expected value is computed
by Block.requests, Block.assumptions, or a second implementation of the pass. -/
structure ExpectedRequest where
  owner : String
  goal : Option String
  assumptions : Array String
  parameters : Array String
  context : List String

def requestMatches (r : CheckRequest) (e : ExpectedRequest) : Bool :=
  r.owner == key e.owner && r.parameters.map (·.written.name.text) == e.parameters &&
    slots r.context == e.context && labels r.assumptions == e.assumptions &&
    r.assumptions.all (fun a => a.owner == r.owner && a.context == r.context &&
      a.member.any (·.kind == .assume)) &&
    match r.question, e.goal with
    | .assumptionsSatisfiable, none =>
      r.demand.map (·.root) == r.assumptions
    | .validity g, some label =>
      g.owner == key e.owner && g.context == r.context &&
      g.member.any (fun m => m.kind == .expect && m.label.text == label) &&
      r.demand.map (·.root) == r.assumptions.push g
    | _, _ => false

def requestsMatch (t : Theory) (expected : Array ExpectedRequest) : Bool :=
  t.requests.size == expected.size &&
    (t.requests.zip expected).all (fun (r, e) => requestMatches r e)

def s1 : String := "pub mod skeleton\n\n\
  pub enum Light { Red, Amber, Green }\n\
  pub fn next(l: Light): Light := match l { Light::Red => Light::Green, Light::Green => Light::Amber, Light::Amber => Light::Red, }\n\
  pub fn wait(l: Light, base: Int): Int := match l { Light::Red => base + 30, Light::Amber => base + 5, Light::Green => base, }\n\
  expect cycles(l: Light) { expect back: next(next(next(l))) = l }\n\
  expect waits(l: Light, base: Int) { assume bounded: base <= 100 expect at_most: wait(l, base) <= 130 }\n\
  expect wrong(l: Light) { expect never_red: next(l) != Light::Red }\n"

def s1Expected : Array ExpectedRequest := #[
  ⟨"cycles", none, #[], #["l"], ["l"]⟩,
  ⟨"cycles", some "back", #[], #["l"], ["l"]⟩,
  ⟨"waits", none, #["bounded"], #["l", "base"], ["base", "l"]⟩,
  ⟨"waits", some "at_most", #["bounded"], #["l", "base"], ["base", "l"]⟩,
  ⟨"wrong", none, #[], #["l"], ["l"]⟩,
  ⟨"wrong", some "never_red", #[], #["l"], ["l"]⟩]

/-- Empty parameter lists and empty blocks are admitted by the current parser.
The two nominal enums deliberately share constructor spellings. -/
def blocksSource (n : Nat) : String := "mod skeleton\n\
  enum Light { Red, Green }\n\
  enum Other { Red, Green }\n\
  fn unused(x: Int): Int := let x := x + 1 in let x := x + 2 in x\n\
  expect multi(x: Int, b?: Bool) { expect first: b? assume early: x >= 0 expect second: x <= " ++
  toString n ++ " assume later: x <= 10 }\n\
  expect other(x: Int) { assume own: x > 20 expect goal: x > 10 }\n\
  expect bare() { expect yes: true }\n\
  expect empty() {}\n\
  expect only() { assume impossible: false }\n\
  expect vacuous() { expect no: false assume contradiction: false }\n"

def blocksExpected : Array ExpectedRequest := #[
  ⟨"multi", none, #["early", "later"], #["x", "b?"], ["b?", "x"]⟩,
  ⟨"multi", some "first", #["early", "later"], #["x", "b?"], ["b?", "x"]⟩,
  ⟨"multi", some "second", #["early", "later"], #["x", "b?"], ["b?", "x"]⟩,
  ⟨"other", none, #["own"], #["x"], ["x"]⟩,
  ⟨"other", some "goal", #["own"], #["x"], ["x"]⟩,
  ⟨"bare", none, #[], #[], []⟩, ⟨"bare", some "yes", #[], #[], []⟩,
  ⟨"empty", none, #[], #[], []⟩,
  ⟨"only", none, #["impossible"], #[], []⟩,
  ⟨"vacuous", none, #["contradiction"], #[], []⟩,
  ⟨"vacuous", some "no", #["contradiction"], #[], []⟩]

def blocksAudit (t : Theory) : Bool :=
  requestsMatch t blocksExpected &&
  declarationIds t == (#["Light", "Other", "unused", "multi", "other", "bare", "empty", "only", "vacuous"]).map key &&
  match block t "multi", block t "empty", function t "unused" with
  | some b, some empty, some f =>
    labels b.members == #["first", "early", "second", "later"] &&
    b.members.all (fun m => m.type == .bool && m.context == b.context) &&
    empty.members.isEmpty && empty.parameters.isEmpty && empty.context.isEmpty &&
    f.signature.parameters.map (·.written.name.text) == #["x"] &&
    slots f.definition.context == ["x"] &&
    -- Three same-spelled binders must still have distinct tokens and slots.
    f.definition.occurrences.any (fun o => slots o.context == ["x", "x", "x"] &&
      (o.context.map (·.1.slice)).eraseDups.length == 3)
  | _, _, _ => false

end FrenThirToMirTests
