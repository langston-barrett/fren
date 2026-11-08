-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- A separate mode leaves every older seed's entire spec unchanged.
Every spec exercises indexed nested constructor arms, fields and results
at one of the types, definitions and comparisons, and a conservative
fallback. `Nat` uses a concrete datatype
and integer sequences: it is not a legal type argument, collection element
or recursive payload.
String comparisons opt out of the decidable core. No deliberate errors. -/
def matchPaths : R String := do
  let ty ← pick #["Int", "Nat", "Bool", "String", "Set<Int>", "Rel<Int, Int>",
    "Seq<Int>", "Option<Int>"]
  let natural := ty == "Nat"
  let ctor := if natural then "MpNat" else "Mp"
  let nodeType := if natural then "MpNat" else s!"Mp<{ty}>"
  let innerCtor := if natural then "MpNatLeaf" else ctor
  let elemType := if natural then "Int" else ty
  let name := if ty == "Bool" then "by_type?" else "by_type"
  let value := if ty == "Bool" then "value?" else "value"
  let resultDecl := if ty == "Bool" then value else s!"{value}: {ty}"
  let positive := if natural then "    require positive: values[0] >= 0\n" else ""
  let offset ← below 8
  let arms := s!"{innerCtor}::A(_) => q[0] + {offset + 1}, {innerCtor}::B(_) => q[0] + {offset + 2}, " ++
    s!"{innerCtor}::Unit => q[0] + {offset + 3}" ++
    (if natural then "" else s!", {ctor}::Box(_) => q[0] + {offset + 4}")
  let nested := s!"match node \{ {ctor}::A(_) => q[0] + 1, {ctor}::B(_) => q[0] + 2, " ++
    s!"{ctor}::Unit => q[0] + 3, {ctor}::Box(part) => match part \{ {arms} } }"
  let fallback ← pick #[
    "Mc::A(_) if flag? => q[0], Mc::B(_) => q[0] + 1, _ => q[0] + 2",
    "Mc::A(_) => q[0], Mc::B(_) if flag? => q[0] + 1, _ => q[0] + 2",
    "Mc::A(0) => q[0], Mc::A(_) => q[0] + 1, _ => q[0] + 2",
    "Mc::Box(Mc::Unit) => q[0], Mc::B(_) => q[0] + 1, _ => q[0] + 2",
    "Mc::A(_) | Mc::Unit => q[0], Mc::B(_) => q[0] + 1, _ => q[0] + 2",
    "Mc::B(_) => q[0], Mc::A(0) => q[0] + 1, _ => q[0] + 2",
    "Mc::A(_) => q[0], rest => q[0] + 1"]
  let body := s!"match control \{ {fallback} }"
  let typedArms := s!"{innerCtor}::A(_) => values[0], {innerCtor}::B(_) => values[0], " ++
    s!"{innerCtor}::Unit => values[0]" ++
    (if natural then "" else s!", {ctor}::Box(_) => values[0]")
  let typedBody := s!"match node \{ {ctor}::A(_) => values[0], {ctor}::B(_) => values[0], " ++
    s!"{ctor}::Unit => values[0], {ctor}::Box(part) => match part \{ {typedArms} } }"
  let natLeaf := "MpNatLeaf::A(n) => (let observed := values[0] in n), " ++
    "MpNatLeaf::B(n) => (let observed := values[0] in n), " ++
    "MpNatLeaf::Unit => (let observed := values[0] in 0)"
  let typedBody := if natural then
      "match node { MpNat::A(n) => (let observed := values[0] in n), " ++
      "MpNat::B(n) => (let observed := values[0] in n), " ++
      s!"MpNat::Unit => (let observed := values[0] in 0), MpNat::Box(part) => match part \{ {natLeaf} } }"
    else typedBody
  let resultLaw := if natural then s!"{value} >= 0" else s!"{value} = values[0]"
  let applicationLaw := if natural then s!"{name}(node, values) >= 0" else s!"{name}(node, values) = values[0]"
  return "mod match_paths\n" ++
    "set_option fren.lint.unused_variables \"allow\"\n" ++
    "set_option fren.lint.undecidable \"allow\"\n" ++
    "pub enum Mp<T> { A(T), B(T), Unit, Box(Mp<T>) }\n" ++
    "pub enum MpNatLeaf { A(Nat), B(Nat), Unit }\n" ++
    "pub enum MpNat { A(Nat), B(Nat), Unit, Box(MpNatLeaf) }\n" ++
    "pub enum Mc { A(Int), B(Bool), Box(Mc), Unit }\n" ++
    s!"pub fn defined(node: {nodeType}, q: Seq<Int>): (value: Int) \{\n" ++
    s!"    require nonempty: q != []\n    out value := {nested}\n" ++
    "    ensure bound: value >= q[0]\n}\n" ++
    s!"pub fn {name}(node: {nodeType}, values: Seq<{elemType}>): ({resultDecl}) \{\n" ++
    s!"    require nonempty: values != []\n{positive}    out {value} := {typedBody}\n" ++
    s!"    ensure result: {resultLaw}\n" ++ "}\n" ++
    s!"pub proc paths(node: {nodeType}, control: Mc, q: Seq<Int>, values: Seq<{elemType}>, flag?) \{\n" ++
    s!"    require nonempty: q != []\n    require values_nonempty: values != []\n{positive}" ++
    s!"    expect result_type: {applicationLaw}\n" ++
    s!"    expect direct: ({nested}) >= q[0]\n" ++
    "    expect definition: defined(node, q) >= q[0]\n" ++
    s!"    expect fallback: ({body}) >= q[0]\n}\n"

end FrenTest.FuzzFrontends.Wide
