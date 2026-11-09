module

public import FrenLirToOir
public import FrenFlatToLirTests.Probe

public section
namespace FrenLirToOirTests
open FrenLir FrenOir FrenModule FrenEval

structure Compiled where
  admitted : FrenThirDesugar.Program
  program : FrenOir.Program
  produced : FrenLirToOir.produce admitted = .ok program

def compile (file : Nat) (source : String) : Except String Compiled := do
  let p ← (FrenThirDesugar.fromSource ⟨file⟩ source).mapError reprStr
  match h : FrenLirToOir.produce p with
  | .error e => .error (reprStr e)
  | .ok out => .ok ⟨p, out, h⟩

def load (source : String) : IO Compiled :=
  match compile 601 source with
  | .ok c => pure c
  | .error e => throw (IO.userError e)

def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

def key (s : String) : FrenBase.ItemId := FrenBase.ItemId.root.named "oir_walk" |>.named s

def strip : Nat → Term → Term
  | 0, t => t
  | n + 1, .at _ t => strip n t
  | _, t => t

def nonzero (q : FrenOir.Question) : Bool := match q.condition with
  | .binary .ne _ (.int 0) => true
  | _ => false

def owned (p : FrenOir.Program) (name : String) : Array FrenOir.Question :=
  p.questions.filter (fun q => q.owner == key name)

def divisions (p : FrenOir.Program) (name : String) : Array FrenOir.Question :=
  (owned p name).filter nonzero

def label (q : FrenOir.Question) : Option String :=
  q.subject.bind (fun b => b.member.map (·.label.text))

def one? (p : FrenOir.Program) (name : String) (kind : Kind)
    (member : Option String := none) : Option FrenOir.Question := do
  let selected := (owned p name).filter (fun q => q.kind == kind && label q == member)
  if selected.size == 1 then selected[0]? else none

/-- Reuse the established test-only finite Term observer, not extraction or a
solver. Interpret only the fixture's constant function, independently of its
emitted equations; all other calls are unsupported by this probe. -/
def symbols : FrenFlatToLirTests.Symbols := fun id component args =>
  if id == key "constant" then
    match args with
    | [.int _] => some (if component == .domain then .bool true else .int 0)
    | _ => none
  else none

def observation (q : FrenOir.Question) (args : Array Value) : Option Bool := do
  if args.size != q.parameters.size then none
  else
    -- Parameters range over total typed values; their domain components are
    -- true. This is not an extra block assumption or a bounded Int domain.
    let .bool result ← FrenFlatToLirTests.observe 1000 symbols
      (args.toList.reverse.map (fun v => (v, true))) q.search | none
    some result

def sees (q : FrenOir.Question) (args : Array Value) (expected : Bool) : Bool :=
  observation q args == some expected

def sorted (p : FrenOir.Program) (q : FrenOir.Question) : Bool :=
  Term.infer 10000 p.lir.mir.source q.context q.search == some .bool

def graphAudit (p : FrenOir.Program) : Bool := Id.run do
  for i in [:p.questions.size] do
    let some q := p.questions[i]? | return false
    if q.id != i || !sorted p q then return false
    if q.kind == .functionDefinedness && (!q.hypotheses.isEmpty || q.request.isSome) then return false
    for dep in q.dependencies do
      match dep with
      | .question id => if id >= p.questions.size then return false
      | .definition id => if !p.definitions.any (fun d => d.signature.id == id) then return false
    if let some body := q.subject then
      if body.owner != q.owner then return false
      if let some o := q.origin then
        if o.owner != q.owner || o.member != body.member ||
            !body.occurrences.any (fun a => a.expression == o.expression && a.context == o.context) then
          return false
  return true

end FrenLirToOirTests
