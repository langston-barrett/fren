import FrenCli.Search

/-!
# Datatype parameters within collections

The generator for `fren_fuzz_frontends --datatype-elements`, kept apart
from the existing generators so their seeds and random draws stay fixed.
-/

namespace FrenTest.FuzzDatatypeElements

open FrenCli.Eval

/-- A payload or field's declared type and a value of it built from the
placeholder `VALUE`. `T` is its declaration's parameter. -/
structure Shape where
  ty : String
  value : String

/-- A collection at the root, and up to three further levels of sets,
sequences, relations, prelude instances and user records. Relations put
`T` on either side, or both. A relation is only drawn around a type with
no relation in it: the Lean front end cannot derive the equality of a
datatype whose field nests relations within relations on both sides, as
`Rel<Rel<Rel<Int, Int>, Rel<Int, Int>>, Rel<Rel<Int, Int>, Rel<Int, Int>>>`,
with or without type parameters, which the umbrella issue for front-end
differences tracks. -/
def collection (inner : Shape) : R Shape := do
  match ← below (if (inner.ty.splitOn "Rel<").length > 1 then 2 else 5) with
  | 0 => return ⟨s!"Set<{inner.ty}>", "{" ++ inner.value ++ "}"⟩
  | 1 => return ⟨s!"Seq<{inner.ty}>", "[" ++ inner.value ++ "]"⟩
  | 2 => return ⟨s!"Rel<{inner.ty}, Int>", "{(" ++ inner.value ++ ", 0)}"⟩
  | 3 => return ⟨s!"Rel<Int, {inner.ty}>", "{(0, " ++ inner.value ++ ")}"⟩
  | _ => return ⟨s!"Rel<{inner.ty}, {inner.ty}>", "{(" ++ inner.value ++ ", " ++ inner.value ++ ")}"⟩

def shape : Nat → R Shape
  | 0 => pure ⟨"T", "VALUE"⟩
  | n + 1 => do
    let inner ← shape n
    match ← below 4 with
    | 0 => return ⟨s!"Option<{inner.ty}>", s!"Option::Some({inner.value})"⟩
    | 1 => return ⟨s!"Box<{inner.ty}>", "Box { value := " ++ inner.value ++ " }"⟩
    | _ => collection inner

/-- A well-typed spec, with enum payloads and record fields at a varied
instance, generic definitions, contracts, constructors, matches, field
reads and updates, constants and comparisons. Some expectations fail;
none introduces a static error that would stop the remaining checks. -/
def spec : R String := do
  let depth ← below 4
  let sh ← collection (← shape depth)
  let bases := #[ ("Int", "x: Int", "1"), ("Bool", "x?", "true"),
    ("String", "x: String", "\"a\""), ("Key", "x: Key", "Key::A"),
    ("Ms", "x: Ms", "Ms(1)"), ("Option<Int>", "x: Option<Int>", "Option::Some(1)"),
    ("Box<Bool>", "x: Box<Bool>", "Box { value := true }"),
    ("Set<Int>", "x: Set<Int>", "{1}"), ("Seq<Bool>", "x: Seq<Bool>", "[true]"),
    ("Rel<Int, Bool>", "x: Rel<Int, Bool>", "{(1, true)}") ]
  let (base, binder, literal) := bases[← below bases.size]!
  let ty := sh.ty.replace "T" base
  let value := if base == "Bool" then sh.value.replace "VALUE" "x?" else sh.value.replace "VALUE" "x"
  let closed := sh.value.replace "VALUE" literal
  let comparison := #["=", "!="][← below 2]!
  let rhs := #["v", "w"][← below 2]!
  let recursive ← below 4
  let recDecls := if recursive == 0 then
    s!"pub enum Chain<T> \{ Nil, Cons({sh.ty}, Chain<T>) }\n" ++
    "pub fn length<T>(c: Chain<T>): Int := match c { Chain::Nil => 0, Chain::Cons(_, tail) => 1 + length(tail) }\n"
    else ""
  let recChecks := if recursive == 0 then
    s!"    expect recursive: let tail: Chain<{base}> := Chain::Nil in length(Chain::Cons(v, tail)) = 1 + length(tail)\n" ++
    "    expect recursive_model: length(Chain::Cons(v, Chain::Nil)) = 0\n"
    else ""
  let evidence ← below 5
  let directive := if evidence == 0 && depth == 0 && (base == "Bool" || base == "Key") then
    "set_option fren.enumeration.size 2 in\nset_option fren.evidence \"enumerated\" in\n" else ""
  return "set_option fren.lint.dead_code \"allow\"\n" ++
    "set_option fren.lint.undecidable \"allow\"\nmod datatype_fuzz\n" ++
    "pub enum Key { A, B }\npub struct Ms(Int)\npub struct Box<T> { value: T }\n" ++
    s!"pub enum Payload<T> \{ Full({sh.ty}) }\n" ++
    s!"pub struct Record<T> \{ value: {sh.ty} }\n" ++
    s!"pub fn get<T>(p: Payload<T>): {sh.ty} := match p \{ Payload::Full(v) => v }\n" ++
    s!"pub fn make<T>(v: {sh.ty}): (r: Payload<T>) \{\n" ++
    "    out r := Payload::Full(v)\n    ensure roundtrip: get(r) = v\n}\n" ++
    s!"pub const CLOSED: Payload<{base}> := Payload::Full({closed})\n" ++ recDecls ++ directive ++
    s!"pub proc check({binder}, v: {ty}, w: {ty}) \{\n" ++
    "    expect roundtrip: get(make(v)) = v\n" ++
    s!"    expect comparison: get(make(v)) {comparison} {rhs}\n" ++
    s!"    expect literal: get(Payload::Full({value})) = {value}\n" ++
    "    expect field: (Record { value := v }).value = v\n" ++
    "    expect update: { Record { value := v } with value := w }.value = w\n" ++
    s!"    expect constant: get(CLOSED) = {closed}\n" ++ recChecks ++
    "}\n"

end FrenTest.FuzzDatatypeElements
