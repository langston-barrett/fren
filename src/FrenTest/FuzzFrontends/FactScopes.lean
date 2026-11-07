-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- Compare reports on separate queries of one item that mention disjoint
contracts, or no function at all (#766). These exercise transitive contract
chains over scalar, collection and compound results, sometimes nested in a
generic record, a defined identity, a `let`, a `where`, a quantifier, a
conditional, a match or a table. The mode checks agreement on the chain,
separate contract and plain cover goal; the UI fixture pins their expected
results. Its independent mode leaves existing seeds and draws unchanged. -/
def factScopes : R String := do
  let k ← below 4
  let (decls, ty, value) ← pick #[
    ("", "Int", toString k), ("", "Nat", toString k),
    ("", "Bool", "true"), ("", "String", "\"scope\""),
    ("", "Set<Int>", s!"\{{k}}"), ("", "Rel<Int, Int>", s!"\{({k}, {k + 1})}"),
    ("", "Seq<Int>", s!"[{k}, {k + 1}]"),
    ("pub enum ScE { A, B }\n", "ScE", "ScE::A"),
    ("pub enum ScP { A, B(Int) }\n", "ScP", s!"ScP::B({k})"),
    ("pub struct ScN(Int)\n", "ScN", s!"ScN({k})"),
    ("pub struct ScBox<T> { v: T }\n", "ScBox<Seq<Int>>", s!"ScBox \{ v := [{k}] }")]
  let r := if ty == "Bool" then "r?" else "r"
  let name (i : Nat) := s!"sc{i}{if ty == "Bool" then "?" else ""}"
  let mut out := "set_option fren.lint.undecidable \"allow\"\n" ++ decls ++
    s!"pub fn {name 0}(x: Int): ({r}: {ty}) \{ ensure e: {r} = {value} }\n"
  let n := (← below 3) + 1
  for i in [1:n + 1] do
    out := out ++ s!"pub fn {name i}(x: Int): ({r}: {ty}) \{ ensure e: {r} = {name (i - 1)}(x) }\n"
  let app := s!"{name n}(x)"
  let (extra, goal) ← match ← below 9 with
    | 0 => pure ("", s!"{app} = {value}")
    | 1 => pure ("", s!"(({app})) = {value}")
    | 2 => pure ("pub fn sc_id<T>(v: T): T := v\n", s!"sc_id({app}) = {value}")
    | 3 => pure ("", s!"(let {r} := {app} in {r}) = {value}")
    | 4 => pure ("", s!"{r} = {value} where {r} := {app}")
    | 5 => pure ("", s!"(if x > {k} then {app} else {name n}(x + 1)) = {value}")
    | 6 => pure ("", s!"(match (x > {k}) \{ true => {app}, false => {name n}(x + 1) }) = {value}")
    | 7 => pure ("", s!"(table \{ x > {k} => {app}, _ => {name n}(x + 1) }) = {value}")
    | _ => pure ("", s!"forall (j: Int), when {k} <= j < {k + 2}, {name n}(j) = {value}")
  -- Other comparisons of ordered results exercise closure at those sites.
  let goal ← if ty == "Int" || ty == "Nat" then
    pick #[goal, s!"{app} >= {k}", s!"{app} <= {k}", s!"{app} < {k + 1}", s!"{app} > {k} - 1",
      s!"{app} != {k + 1}"]
    else pure goal
  return out ++ extra ++ "pub fn sc_other(x: Int): (r: Int) { ensure e: r < 0 }\n" ++
    s!"proc sc_queries(x: Int) \{\n    expect chain: {goal}\n    expect separate: sc_other(x) < 0\n" ++
    s!"    cover plain: x = {k}\n}\n"

end FrenTest.FuzzFrontends.Wide
