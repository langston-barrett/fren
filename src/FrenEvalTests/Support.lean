module

public import FrenEval

public section
namespace FrenEvalTests
open FrenEval

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def key (name : String) : FrenBase.ItemId := FrenBase.ItemId.root.named "skeleton" |>.named name

def light (ctor : String) : Value := .enum (key "Light") ((key "Light").named ctor)

def load (source : String) : IO Program :=
  match fromSource ⟨101⟩ source with
  | .ok p => pure p
  | .error d => throw (IO.userError s!"evaluator fixture rejected: {repr d}\n{source}")

def result (p : Program) (name : String) (values : Array Value := #[.int 0])
    (member : Option String := none) (depth : Nat := defaultDepth p) : Outcome :=
  match evaluate p ⟨key name, member⟩ values depth with
  | .ok evaluation => evaluation.outcome
  | .error d => .error d

def hasValue (outcome : Outcome) (expected : Value) : Bool :=
  match outcome with | .ok v => v == expected | _ => false

def isUndefined (outcome : Outcome) : Bool :=
  match outcome with | .error (.undefined ..) => true | _ => false

def isInvalid (outcome : Outcome) : Bool :=
  match outcome with | .error (.invalid ..) => true | _ => false

def isExhausted (outcome : Outcome) : Bool :=
  match outcome with | .error (.exhausted _) => true | _ => false

def s1 : String := "pub mod skeleton\n\n\
  pub enum Light { Red, Amber, Green }\n\
  pub fn next(l: Light): Light := match l {\n\
    Light::Red => Light::Green,\n\
    Light::Green => Light::Amber,\n\
    Light::Amber => Light::Red,\n}\n\
  pub fn wait(l: Light, base: Int): Int := match l {\n\
    Light::Red => base + 30,\n\
    Light::Amber => base + 5,\n\
    Light::Green => base,\n}\n\
  expect cycles(l: Light) { expect back: next(next(next(l))) = l }\n\
  expect waits(l: Light, base: Int) {\n\
    assume bounded: base <= 100\n\
    expect at_most: wait(l, base) <= 130\n}\n\
  expect wrong(l: Light) { expect never_red: next(l) != Light::Red }\n"

end FrenEvalTests
