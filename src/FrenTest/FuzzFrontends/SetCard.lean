-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- The set procedure from #818's decidable-core mode, with its original
random draws (three for strings before the three for sets), so that #820's
seed numbers reproduce the same checks independently of the other
decidable-core procedures. Preconditions use the current `require` spelling. -/
def setCardCore : R String := do
  for _ in [0:3] do discard (below 2147483648)
  let mut out := "mod sets\n\nset_option fren.lint.unused_variables \"allow\"\n\nenum E { A, B, C }\n\n"
  let sets := #["s", "t", "(s union t)", "(s inter t)", "(s minus t)", "{1, 2}", "(t minus t)"]
  let mut atoms : Array String := #[]
  for _ in [0:3] do
    let seed ← below 2147483648
    let pick (xs : Array String) (salt : Nat) := xs[(seed / (salt + 7)) % xs.size]!
    let a := pick sets 1
    let b := pick sets 2
    let i := toString ((seed / 13) % 4)
    atoms := atoms.push <| pick #[
      s!"x in {a}", s!"{a} subset {b}", s!"{a} = {b}", s!"{a} != {b}", s!"{a}.card <= {i}",
      s!"{a}.card + {b}.card >= {i}", s!"e in es", "es = {E::A, E::B}", s!"es.card = {i}", "x in s and not x in t",
      "s = {}"] 5
  out := out ++ s!"proc c0(s: Set<Int>, t: Set<Int>, x: Int, es: Set<E>, e: E): (p?) \{\n    \
    require a: not ({atoms[0]!} and {atoms[1]!})\n\n    ensure r: p? iff ({atoms[1]!} or {atoms[2]!})\n\n    \
    expect g: when p?, {atoms[0]!} or {atoms[2]!}\n}\n\n"
  return out

/-- Finite cardinalities in each representation that the lowering can
list: Booleans, variants, generic payloads, records, newtypes and pairs;
under algebra, definitions, nesting, and every integer comparison. Draws
come after `setCardCore`, preserving every original regression. -/
def setCardForms : R String := do
  let decls := "mod card_forms\n\nset_option fren.lint.unused_variables \"allow\"\n\n" ++
    "enum E { A, B, C }\n\nenum G<T> { A, B(T) }\n\nstruct R<T> { x: T, y? }\n\n" ++
    "struct N(Bool)\n\n"
  let types := #[
    ("Bool", "true", 2), ("E", "E::B", 3), ("G<Bool>", "G::B(true)", 3),
    ("R<E>", "R { x := E::A, y? := true }", 6),
    ("N", "N(true)", 2), ("G<R<Bool>>", "G::B(R { x := false, y? := true })", 5),
    ("Option<Bool>", "Option::Some(true)", 3), ("Result<E, Bool>", "Result::Ok(E::A)", 5)]
  let (ty, value, count) ← pick types
  let recv ← pick #["s", "(s union t)", "(s inter t)", "(s minus t)", "{one}"]
  let op ← pick #["=", "!=", "<", "<=", ">", ">="]
  let bound ← below (count + 2)
  let (other, otherValue, otherCount) ← pick types
  let binder := if ty == "Bool" then "x?" else "x"
  let claim := s!"{recv}.card {op} {bound}"
  -- A typed constant also supplies Result's parameter absent from `Ok`.
  let body := s!"const one: {ty} := {value}\n\nfn count(s: Set<{ty}>): Int := s.card\n\n" ++
    s!"proc forms(s: Set<{ty}>, t: Set<{ty}>): (n: Int) \{\n    out n := {recv}.card\n\n" ++
    s!"    expect bounds: 0 <= n <= {count}\n\n" ++
    s!"    expect defined: count({recv}) = n\n\n" ++
    s!"    expect singleton: when s = \{{value}}, s.card = 1\n\n" ++
    s!"    expect comparison: ({claim}) iff (n {op} {bound})\n}\n\n" ++
    s!"proc full(s: Set<{ty}>) \{\n    require all: forall ({binder}: {ty}), {binder} in s\n\n    expect count: s.card = {count}\n}\n\n" ++
    s!"proc pairs(r: Rel<{ty}, {other}>): (n: Int) \{\n    out n := r.card\n\n    expect bound: 0 <= n <= {count * otherCount}\n\n" ++
    s!"    expect singleton: when r = \{({value}, {otherValue})}, n = 1\n}\n"
  return decls ++ body

/-- Cardinality in quantifier bodies and function contracts. These draws
follow every existing cardinality draw, retaining the old spec as a prefix. -/
def setCardNested : R String := do
  let (ty, count) ← pick #[("Bool", 2), ("E", 3), ("G<Bool>", 3), ("R<E>", 6),
    ("N", 2), ("G<R<Bool>>", 5), ("Option<Bool>", 3), ("Result<E, Bool>", 5)]
  let binder := if ty == "Bool" then "x?" else "x"
  return "\nmod card_nested\n\n" ++
    "pub enum E { A, B, C }\n\npub enum G<T> { A, B(T) }\n\n" ++
    "pub struct R<T> { x: T, y? }\n\npub struct N(Bool)\n\n" ++
    s!"pub fn count(s: Set<{ty}>): (n: Int) \{\n    out n := s.card\n\n" ++
    s!"    ensure bound: 0 <= n <= {count}\n}\n\n" ++
    s!"proc nested(s: Set<{ty}>) \{\n" ++
    s!"    expect monotone: forall ({binder}: {ty}), (s union \{{binder}}).card >= s.card\n\n" ++
    s!"    expect contract: count(s) <= {count}\n}\n"

def genSetCard : R String := do
  let original := (← setCardCore) ++ "\n" ++ (← setCardForms)
  return original ++ (← setCardNested)

end FrenTest.FuzzFrontends.Wide
