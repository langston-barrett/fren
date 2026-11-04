import FrenCli.Search

/-! Singleton clients of the structural-group checker. Deliberate errors
have their own fuzzer mode, so they cannot suppress another spec's checks. -/

namespace FrenTest.FuzzRecursion

open FrenCli.Eval

private def pick (xs : Array α) [Inhabited α] : R α := do
  return xs[← below xs.size]!

def gen : R String := do
  let generic := (← below 2) == 0
  let kind ← below 9
  let n := if kind == 8 then 1 else (← below 4) + 1
  let pos ← below n
  let (ty, value) ← pick (#[ ("Int", "0"), ("Nat", "0"), ("Bool", "false"), ("String", "\"\""),
    ("Set<Int>", "{}"), ("Rel<Int, Int>", "{}"), ("Seq<Int>", "[]"), ("Option<Int>", "Option::None") ] ++
    (if generic then #[("T", "v")] else #[]))
  let tree := if generic then "Rg<T>" else "Rg"
  let (ty, value) := if (← below 10) == 0 then (tree, s!"x{pos}") else (ty, value)
  let tps := if generic then "<T>" else ""
  let params := (List.range n).map fun i => s!"x{i}: {tree}"
  let args (child : String) := ", ".intercalate ((List.range n).map fun i => if i == pos then child else s!"x{i}")
  let call (child : String) := s!"rg_step({args child})"
  let applyName := if ty == "Bool" then "rg_apply?" else "rg_apply"
  let nested := (← below 2) == 0
  let binder := if ty == "T" then "v" else "_"
  let leaf := s!"Rg::Leaf({binder}) => {value}"
  let body ← match kind with
    | 0 | 1 | 2 | 3 => pure (call "l")
    | 4 => pure (call s!"x{pos}")
    | 5 => pure (call "Rg::Node(l, l)")
    | 6 => pure s!"let child := l in {call "child"}"
    | 7 => pure s!"{applyName}(|child| {call "child"}, l)"
    | _ => pure s!"{applyName}(rg_step, l)"
  let mut out := "set_option fren.lint.style \"allow\"\nset_option fren.lint.restriction \"allow\"\n" ++
    "set_option fren.lint.unused_variables \"allow\"\n" ++
    s!"pub enum Rg{tps} \{ Leaf({if generic then "T" else "Int"}), Node({tree}, {tree}) }\n"
  if kind ≥ 7 then
    out := out ++ s!"pub fn {applyName}{tps}(g: fn({tree}) -> {ty}, x: {tree}): {ty} := g(x)\n"
  let branch := if nested then s!"Rg::Node(Rg::Node(l, _), _) => {body}, Rg::Node(l, _) => {body}"
    else s!"Rg::Node(l, _) => {body}"
  let expression := s!"match x{pos} \{ {leaf}, {branch} }"
  let name := if ty == "Bool" then "rg_step?" else "rg_step"
  let expression := (expression.replace "rg_step(" s!"{name}(").replace "(rg_step," s!"({name},"
  let comparison ← if ty == "Int" || ty == "Nat" then pick #["=", "!=", "<", "<=", ">", ">="]
    else if ty == "Set<Int>" || ty == "Rel<Int, Int>" then pick #["=", "!=", "subset"] else pick #["=", "!="]
  let test := if kind < 4 then
      let base := if ty == "T" then "0" else if ty == tree then "Rg::Leaf(0)" else value
      s!"expect rg_value: {name}({", ".intercalate ((List.range n).map fun _ => "Rg::Leaf(0)")}) {comparison} {base}\n"
    else ""
  if (← below 2) == 0 then
    return out ++ s!"pub fn {name}{tps}({", ".intercalate params}): {ty} := {expression}\n" ++ test
  else
    let result := if ty == "Bool" then "r?" else "r"
    return out ++ s!"pub fn {name}{tps}({", ".intercalate params}): ({result}: {ty}) \{\n    out {result} := {expression}\n}\n" ++ test

end FrenTest.FuzzRecursion
