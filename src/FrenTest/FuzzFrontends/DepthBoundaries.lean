-- keep-sorted start
import Lean
-- keep-sorted end

namespace FrenTest.FuzzFrontends

/-- The quantifier cases beyond the boundary are refused. A nonrecursive
call's body is inlined, whereas a recursive body is a separate root. -/
def depthBoundaryRefuses (seed : Nat) : Bool :=
  seed / 6 % 3 == 2 && (seed % 6 == 3 || seed % 6 == 4 ||
    (seed % 6 == 5 && seed / 18 % 2 == 1))

#guard (List.range 54).filter depthBoundaryRefuses == [15, 16, 33, 34, 35, 51, 52]

/-- Depth transport has a separate seed stream: existing modes and every
old corpus source remain unchanged, including intentional refusals. -/
def depthBoundarySpec (seed : Nat) : String :=
  let header := "set_option fren.evidence \"enumerated\"\n" ++
    "set_option fren.enumeration.size 1\n" ++
    "set_option fren.lint.nonminimal_bool \"allow\"\n" ++
    "set_option fren.lint.double_neg \"allow\"\n" ++
    "set_option fren.lint.undecidable \"allow\"\n"
  let near := seed / 6 % 3
  let nots (n : Nat) := String.join (List.replicate n "not ")
  match seed % 6 with
  | 0 =>
    let extra := seed / 18 % 3
    let definition := nots extra ++ (if seed / 54 % 2 == 0 then "x?" else "false")
    let chain := seed / 162 % 2 == 1
    let result := if chain then "z?" else "y?"
    let more := if chain then "    out z? := y?\n" else ""
    header ++ s!"pub proc defined(x?): (det y?{if chain then ", z?" else ""}) \{\n    out y? := {definition}\n" ++ more ++
      s!"    expect boundary: {nots (253 - extra + near - if chain then 1 else 0)}{result}\n}\n"
  | 1 =>
    let forms := #["true or y?", "y? or true", "false and y?", "y? and false",
      "if true then true else y?", "if false then y? else false"]
    let body := forms[seed / 18 % forms.size]!
    header ++ s!"pub proc lazy(x?): (y?) \{\n    out y? := {nots 255}x?\n" ++
      s!"    expect boundary: {body}\n}\n"
  | 2 =>
    let cases := #[("Bool", "true", "false"), ("Int", "0", "1"), ("Nat", "0", "1"),
      ("String", "\"a\"", "\"b\""), ("Seq<Bool>", "[true]", "[false]"),
      ("Set<Bool>", "{true}", "{false}"), ("Rel<Bool, Bool>", "{}", "{(true, false)}"),
      ("Option<Int>", "Option::None", "Option::Some(1)"), ("Box", "Box(0)", "Box(1)"),
      ("RecordValue", "RecordValue { flag? := true }", "RecordValue { flag? := false }")]
    let (ty, first, second) := cases[seed / 18 % cases.size]!
    let name := if ty == "Bool" then "value?" else "value"
    let chosen := if ty == "Bool" then "chosen?" else "chosen"
    let condition := if seed / 180 % 2 == 0 then "true" else "false"
    let value := if condition == "true" then first else second
    header ++ "pub struct Box(Int)\npub struct RecordValue { flag?: Bool }\n" ++
      s!"pub proc value(x?): (y?, det {chosen}: {ty}) \{\n    out y? := {nots 255}x?\n" ++
      s!"    out {chosen} := if {condition} then {first} else if y? then {second} else {second}\n" ++
      s!"    expect output: {chosen} = {value}\n" ++
      s!"    expect boundary: (let {name}: {ty} := if {condition} then {first} else if y? then {second} else {second} in {name}) = {value}\n}\n"
  | 3 =>
    let count := 1 + seed / 18 % 3
    let names := " ".intercalate ((List.range count).map fun k => s!"b{k}?")
    let quant := if seed / 54 % 2 == 0 then "forall" else "exists"
    header ++ s!"pub proc quantified(x?) \{\n    expect boundary: {quant} ({names}: Bool), {nots (254 - count + near)}x?\n}\n"
  | 4 =>
    let count := 1 + seed / 18 % 3
    let names := " ".intercalate ((List.range count).map fun k => s!"b{k}?")
    let dependent := count > 1 && seed / 54 % 2 == 1
    let declaration := "pub fn read?(Bool): Bool\n"
    let call := if dependent then "read?(b0?)" else "read?(true)"
    let cost := 2
    header ++ declaration ++ s!"pub proc lifted() \{\n    expect boundary: forall ({names}: Bool), {nots (255 - count - cost + near)}{call}\n}\n"
  | _ =>
    let deep := nots (250 + near)
    let recursive := seed / 18 % 2 == 0
    let tail := if recursive then "f?(a, b?)" else "b?"
    header ++ "pub enum T { Z, S(T) }\n" ++
      s!"pub fn f?(t: T, b?): Bool := match t \{ T::Z => b?, T::S(a) => {tail} }\n" ++
      s!"pub proc vector(b?) \{ expect boundary: {deep}(match f?(T::Z, b?), true \{ true, true => true, _, _ => false }) }\n"

end FrenTest.FuzzFrontends
