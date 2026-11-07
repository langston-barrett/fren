-- keep-sorted start
import Lean
-- keep-sorted end

namespace FrenTest.FuzzFrontends

/-- Resource-bound probes have a mode of their own, so every old seed keeps
its source. They cover large type unfoldings and function domains as well as
ordinary types, nesting, definitions and comparisons within the budget. -/
def resourceBaseSpec (seed : Nat) : String :=
  let header := "mod fz_resources\nset_option fren.evidence \"enumerated\"\n" ++
    "set_option fren.lint.undecidable \"allow\"\n" ++
    "set_option fren.lint.let_and_return \"allow\"\n" ++
    "set_option fren.lint.assertions_on_constants \"allow\"\n"
  let types := #["Bool", "Int", "Nat", "String", "Seq<Bool>", "Set<Bool>", "Rel<Bool, Bool>", "Leaf"]
  let base := types[(seed / 32) % types.size]!
  -- Nat is permitted directly and in a newtype, but not as a generic
  -- argument or collection element.
  let element := if base == "Nat" then "Int" else base
  let leaf := "pub struct Leaf { flag?: Bool, number: Int }\n"
  let args := ", ".intercalate (List.replicate 64 "Bool")
  let values := ", ".intercalate (List.replicate 64 (if seed % 2 == 0 then "false" else "true"))
  match seed % 32 with
  | 0 => header ++ s!"pub fn choose?({args}): Bool\npub proc spec() \{ expect e: choose?({values}) or not choose?({values}) }\n"
  | 1 => header ++ s!"pub enum One \{ Only }\npub fn choose({args}): One\npub proc spec() \{ expect e: choose({values}) = One::Only }\n"
  | 2 => header ++ "set_option fren.enumeration.size 64\n" ++
      "pub enum Tree { Leaf, Node(Tree, Tree) }\npub proc spec(x: Tree) { expect e: x = x }\n"
  | 3 => header ++ leaf ++ "set_option fren.enumeration.size 64\n" ++
      "pub enum Tree<A> { Leaf(A), Node(Tree<A>, Tree<A>) }\n" ++
      s!"pub struct Wrapped(Tree<{element}>)\npub proc spec(x: Wrapped) \{ expect e: x = x }\n"
  | 4 => header ++ "pub proc spec() {\n" ++
      "    expect undecided: forall (i: Int), when 0 <= i < 1024, (forall (x: Int), x = x)\n" ++
      "    expect late: not (forall (i: Int), when 0 <= i < 1024, i < 1023 and (forall (x: Int), x = x))\n}\n"
  | _ =>
    let decls := leaf ++ "pub enum T<A> { Leaf(A), More(T<A>) }\n" ++
      s!"pub struct R<A> \{ value: A, flag?: Bool }\npub struct W({base})\n"
    let ty := match seed % 8 with
      | 0 => base | 1 => s!"Seq<{element}>" | 2 => s!"Set<{element}>" | 3 => s!"Rel<Bool, {element}>"
      | 4 => s!"T<{element}>" | 5 => s!"R<{element}>" | 6 => "W" | _ => s!"Seq<Set<{element}>>"
    let ops := if ty == "Int" || ty == "Nat" || ty == "String" then #["=", "!=", "<", "<=", ">", ">="] else #["=", "!="]
    let op := ops[(seed / 256) % ops.size]!
    let negs := String.join (List.replicate (2 * (seed % 12)) "not ")
    let suffix := if ty == "Bool" then "?" else ""
    header ++ decls ++ s!"pub proc spec(x{suffix}: {ty}): (det y{suffix}: {ty}) \{\n" ++
      s!"    out y{suffix} := let copy{suffix} := x{suffix} in copy{suffix}\n" ++
      s!"    expect e: {negs}(let a{suffix} := y{suffix}, b{suffix} := x{suffix} in a{suffix} {op} b{suffix})\n}\n"

/-- Selected cases, including partial results, appended after the existing
resource fixtures so their declarations and random choices stay unchanged.
Vary the result type, nesting, definitions and comparisons independently. -/
def resourceCaseSpec (seed : Nat) : String := Id.run do
  let cases := #[("Bool", "true", "false"), ("Int", "0", "1"), ("Nat", "LOW", "HIGH"),
    ("String", "\"a\"", "\"b\""), ("Seq<Bool>", "[true]", "[false]"),
    ("Set<Bool>", "{true}", "{false}"), ("Rel<Bool, Bool>", "{(true, true)}", "{(false, false)}"),
    ("Box", "Box(0)", "Box(1)"), ("Tag", "Tag::A", "Tag::B"),
    ("RecordValue", "RecordValue { flag? := true, number := 0 }", "RecordValue { flag? := false, number := 1 }"),
    ("AbstractValue", "x", "y"), ("RecursiveValue", "RecursiveValue::Z", "RecursiveValue::S(RecursiveValue::Z)"),
    ("Holder<Seq<Bool>>", "Holder { value := [true] }", "Holder { value := [false] }")]
  let (ty, left, right) := cases[seed % cases.size]!
  let header := "mod fz_resource_cases\n" ++
    "pub enum Tag { A, B }\npub struct Box(Int)\n" ++
    "pub struct RecordValue { flag?: Bool, number: Int }\npub type AbstractValue\n" ++
    "pub enum RecursiveValue { Z, S(RecursiveValue) }\npub struct Holder<A> { value: A }\n" ++
    "pub fn unknown?(b?): Bool := forall (i: Int), i = i and b?\n" ++
    (if ty == "Nat" then "pub const LOW: Nat := 0\npub const HIGH: Nat := 1\n" else "")
  -- Hidden quantifiers in cases over open values already differ (#493).
  -- Keep abstract results under known conditions, as the confirmation
  -- generator also excludes abstract values from partial evaluation.
  let condition := if ty == "AbstractValue" then "true" else "unknown?(true)"
  let mut body := s!"if {condition} then {left} else {right}"
  -- Collections, records, newtypes and abstract values cannot be matched,
  -- even by a wildcard. Vary their result type under a Boolean scrutinee.
  let scrutinee := if ["Bool", "Int", "Nat", "String", "Tag", "RecursiveValue"].contains ty then left else "true"
  for k in [0:2 + (seed / 36) % 4] do
    body := match (seed / 9 + k) % 4 with
      | 0 => s!"match ({scrutinee}) \{ _ => {body} }"
      | 1 => s!"table \{ true => {body}, _ => {right} }"
      | 2 => s!"match Tag::A \{ Tag::A => {body}, Tag::B => {right} }"
      | _ => s!"match {condition} \{ true => {body}, false => {right} }"
  let suffix := if ty == "Bool" then "?" else ""
  let parameters := if ty == "AbstractValue" then "x: AbstractValue, y: AbstractValue" else s!"x{suffix}: {ty}"
  let arguments := if ty == "AbstractValue" then "x, y" else left
  let inputs := if ty == "AbstractValue" then parameters else ""
  let (decl, resultBody) := match (seed / cases.size) % 3 with
    | 0 => ("", body)
    | 1 => (s!"pub fn value{suffix}({parameters}): {ty} := {body}\n", s!"value{suffix}({arguments})")
    | _ => ("", s!"let v{suffix} := {body} in v{suffix}")
  let ops := if ty == "Int" || ty == "Nat" || ty == "String" then #["=", "!=", "<", "<=", ">", ">="] else #["=", "!="]
  let op := ops[(seed / (cases.size * 3)) % ops.size]!
  return header ++ decl ++ s!"pub proc cases({inputs}) \{ expect result: ({resultBody}) {op} {left} }\n"

/-- Boundary cases have their own mode: refusals may stop a check, so they
must not be appended to the existing seeds' otherwise valid specs. -/
def resourceBoundarySpec (seed : Nat) : String :=
  let header := "set_option fren.evidence \"enumerated\"\n" ++
    "set_option fren.lint.nonminimal_bool \"allow\"\n" ++
    "set_option fren.lint.double_neg \"allow\"\n" ++
    "set_option fren.enumeration.size 4\n"
  match seed % 4 with
  | 0 =>
    let types := #["Bool", "Int", "String", "Seq<Bool>", "Set<Bool>", "Rel<Bool, Bool>", "Box", "Tag"]
    let ty := types[(seed / 4) % types.size]!
    let suffix := if ty == "Bool" then "?" else ""
    let negs := String.join (List.replicate (252 + (seed / 32) % 8) "not ")
    let op := if seed % 64 < 32 then "=" else "!="
    header ++ "pub struct Box(Int)\npub enum Tag { A, B }\n" ++
      s!"proc boundary(x{suffix}: {ty}) \{ expect e: {negs}(x{suffix} {op} x{suffix}) }\n"
  | 1 =>
    let tight := seed % 8 == 1
    let negs := String.join (List.replicate (if tight then 249 + (seed / 8) % 6 else 82 + (seed / 8) % 18) "not ")
    (header ++ if tight then "set_option fren.enumeration.size 1\n" else "") ++ "pub enum T { Z, S(T) }\n" ++
      s!"pub fn holds?(t: T): Bool := match t \{ T::Z => true, T::S(a) => {negs}holds?(a) }\n" ++
      "proc p(t: T) { expect e: holds?(t) }\nproc d(t: T): (det y?) { out y? := holds?(t) }\n"
  | _ =>
    let high := toString ((1 : Nat) <<< (80 + seed % 8))
    let pattern := if seed % 4 == 2 then s!"..=0 | {high}" else s!"-{high}..=0"
    -- Enumeration of the procedure below exercises domain construction;
    -- the alias's synthesized checks keep their normal solver evidence.
    header ++ "set_option fren.evidence \"solver\" in\n" ++
      s!"pub type Tiny = x: Nat where tiny: x is {pattern}\n" ++
      "proc finite(x: Tiny) { expect e: x >= 0 }\n"

/-- The original resource spec followed by cases with partial values. -/
def resourceSpec (seed : Nat) : String := resourceBaseSpec seed ++ resourceCaseSpec seed

end FrenTest.FuzzFrontends
