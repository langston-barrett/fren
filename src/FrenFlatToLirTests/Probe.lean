module

public import FrenFlatToLir
public import FrenEval

public section
namespace FrenFlatToLirTests
open FrenLir FrenModule FrenEval

/-- Test-only observation of logical terms under a supplied finite symbol
interpretation. No definition unfolding, source interpreter, solver, failure
classification or production FrenLirEval is implemented here. Unsupported
operand combinations and exhausted probe depth return none, never Boolean false. -/
abbrev Symbols := FrenBase.ItemId → Component → List Value → Option Value
abbrev Slots := List (Value × Bool)

private def primitive (op : FrenAst.BinaryOp) (a b : Value) : Option Value :=
  match op, a, b with
  | .add, .int x, .int y => some (.int (x + y))
  | .sub, .int x, .int y => some (.int (x - y))
  | .mul, .int x, .int y => some (.int (x * y))
  -- Arbitrary totalized value; the domain formula must still reject zero.
  | .div, .int x, .int y => some (.int (if y == 0 then 0 else x / y))
  | .mod, .int x, .int y => some (.int (if y == 0 then 0 else x % y))
  | .lt, .int x, .int y => some (.bool (x < y))
  | .le, .int x, .int y => some (.bool (x ≤ y))
  | .gt, .int x, .int y => some (.bool (x > y))
  | .ge, .int x, .int y => some (.bool (x ≥ y))
  | .and, .bool x, .bool y => some (.bool (x && y))
  | .or, .bool x, .bool y => some (.bool (x || y))
  | .iff, .bool x, .bool y => some (.bool (x == y))
  | .eq, x, y => if x.type == y.type then some (.bool (x == y)) else none
  | .ne, x, y => if x.type == y.type then some (.bool (x != y)) else none
  | _, _, _ => none

def observe : Nat → Symbols → Slots → Term → Option Value
  | 0, _, _, _ => none
  | n + 1, symbols, env, term => do
    let visit := observe n symbols env
    match term with
    | .bool b => some (.bool b)
    | .int i => some (.int i)
    | .constructor owner id => some (.enum owner id)
    | .local _ i component =>
      let (value, domain) ← env[i]?
      some (if component == .domain then .bool domain else value)
    | .unary .not a => do
      let .bool b ← visit a | none
      some (.bool (!b))
    | .unary .neg a => do
      let .int i ← visit a | none
      some (.int (-i))
    | .binary op a b => primitive op (← visit a) (← visit b)
    | .ite c a b => do
      let .bool selected ← visit c | none
      visit (if selected then a else b)
    | .app sig component args => symbols sig.id component (← args.mapM visit)
    | .letE _ _ value domain body =>
      let v ← visit value
      let .bool wd ← visit domain | none
      observe n symbols ((v, wd) :: env) body
    | .at _ term => visit term

structure Compiled where
  admitted : FrenThirDesugar.Program
  program : FrenLir.Program
  produced : FrenFlatToLir.produce admitted = .ok program

def compile (file : Nat) (source : String) : Except String Compiled := do
  let p ← (FrenThirDesugar.fromSource ⟨file⟩ source).mapError reprStr
  match h : FrenFlatToLir.produce p with
  | .error d => .error (reprStr d)
  | .ok out => .ok ⟨p, out, h⟩

def load (source : String) : IO Compiled :=
  match compile 301 source with
  | .error d => throw (IO.userError d)
  | .ok c => pure c

def require (b : Bool) (detail : String) : IO Unit :=
  unless b do throw (IO.userError detail)

def key (s : String) : FrenBase.ItemId := FrenBase.ItemId.root.named "lir_walk" |>.named s

def light (s : String) : Value := .enum (key "Light") ((key "Light").named s)

def body? (p : FrenLir.Program) (name : String) (label : Option String := none) : Option Body := do
  for d in p.declarations do
    match d with
    | .function sig b => if sig.id == key name && label.isNone then return b
    | .block b members =>
      if b.owner == key name then
        if let some found := members.find? (fun m => m.source.member.map (·.label.text) == label) then
          return found
    | _ => pure ()
  none

/-- Independently written finite interpretations for fixture calls, not an
implementation of definition semantics. Bodies are probed separately. -/
def symbols : Symbols := fun id component args => do
  if id == key "ignore" then
    match args with
    | [.int _] => some (if component == .domain then .bool true else .int 0)
    | _ => none
  else if id == key "wait" then
    match args with
    | [.enum owner ctor, .int base] =>
      if owner != key "Light" then none
      else if ctor == (key "Light").named "Red" then
        some (if component == .domain then .bool true else .int (base + 30))
      else if ctor == (key "Light").named "Green" then
        some (if component == .domain then .bool true else .int base)
      else none
    | _ => none
  else none

def observations (b : Body) (args : Array Value) : Option (Value × Bool) := do
  let env := args.toList.reverse.map fun v => (v, true)
  let v ← observe 400 symbols env b.term.value
  let .bool wd ← observe 400 symbols env b.term.defined | none
  return (v, wd)

def sourceOutcome (c : Compiled) (name : String) (args : Array Value)
    (label : Option String := none) (depth : Nat := 200) : Outcome :=
  let evaluator : FrenEval.Program :=
    ⟨c.admitted.input, c.program.mir.source, FrenFlatToLir.admission _ _ c.produced⟩
  match FrenEval.evaluate evaluator ⟨key name, label⟩ args depth with
  | .error d => .error d
  | .ok e => e.outcome

/-- Expected is independent concrete data. Undefined requires a false domain,
not any chosen symbolic value. Invalid/exhausted source outcomes never pass. -/
def agrees (c : Compiled) (name : String) (args : Array Value)
    (expected : Option Value) (label : Option String := none) : Bool := Id.run do
  let some b := body? c.program name label | return false
  let some (v, wd) := observations b args | return false
  match expected, sourceOutcome c name args label with
  | some want, .ok actual => return wd && v == want && actual == want
  | none, .error (.undefined ..) => return !wd
  | _, _ => return false

end FrenFlatToLirTests
