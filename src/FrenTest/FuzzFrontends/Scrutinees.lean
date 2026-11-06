-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- Several scrutinees of every matchable kind, repeated or distinct,
with parentheses, comments, calls (uninterpreted too), methods, fields,
indexes, definitions and nested matches. The result is also used in a
comparison, a definition, a closure and an outer match. This group adds
no static error. A mode of its own (`--scrutinees`) leaves every older
mode's seed unchanged, including diagnostics after an earlier error. -/
def duplicateScrutineeGroup : R String := do
  let mut out := "set_option fren.lint.unused_variables \"allow\"\n" ++
    "set_option fren.lint.undecidable \"allow\"\n" ++
    "pub enum Ds { A, B, C(Int), D(Bool) }\n" ++
    "pub ordered enum Dso { A, B, C }\n" ++
    "pub enum Dsr { End, Next(Dsr) }\n" ++
    "pub struct Dsp { left: Int, right: Int }\n" ++
    "pub fn ds_unknown(Int): Int\n" ++
    "pub fn ds_apply(f: fn(Int) -> Int, x: Int): Int := f(x)\n" ++
    "pub fn ds_id<T>(x: T): T := x\n" ++
    "pub fn ds_implicit(Bool, Bool): Int := match { true, false => 1, _, _ => 0 }\n"
  let params := "n: Int, m: Int, u: Nat, v: Nat, a?, b?, s: String, t: String, r: Ds, z: Ds, " ++
    "o: Dso, h: Dso, opt: Option<Int>, other: Option<Int>, tree: Dsr, branch: Dsr, p: Dsp"
  for k in [:2] do
    let (ty, pairs, pat, otherPat) ← pick #[
      ("Int", #[("n", "m"), ("p.left", "p.right"), ("[n, m][0]", "[n, m][1]"),
        ("ds_unknown(n)", "ds_unknown(m)"), ("n + 1", "1 + n"),
        ("let x := n + 1 in x", "let x := m + 1 in x"),
        ("let x := n + 1 in x + 1", "let x := m + 1 in x + 1"),
        ("match r { Ds::C(x) => x, _ => n }", "match z { Ds::C(x) => x, _ => n }")], "0..=2", "3..=5"),
      ("Nat", #[("u", "v"), ("u + 1", "v + 1"), ("if a? then u else v", "if b? then u else v")], "0", "1"),
      ("Bool", #[("a?", "b?"), ("n > 0", "m > 0"), ("o < h", "o <= h"),
        ("not a?", "not b?"), ("a? and b?", "a? or b?"),
        ("when a?, b?", "unless a?, b?"),
        ("forall (ds_flag?: Bool), ds_flag? or a?", "exists (ds_flag?: Bool), ds_flag? and b?"),
        ("at_most_one?(a?, b?)", "exactly_one?(a?, b?)"),
        ("if r is Ds::C(x) then x > n else a?", "if z is Ds::C(x) then x > n else a?")], "true", "false"),
      ("String", #[("s", "t"), ("s.at(0)", "t.at(0)"), ("s ++ \"a\"", "t ++ \"a\"")], "\"a\"", "\"b\""),
      ("Ds", #[("r", "z"), ("Ds::C(n)", "Ds::C(m)"), ("if a? then r else z", "if b? then r else z")], "Ds::A", "Ds::C(_)"),
      ("Dso", #[("o", "h")], "Dso::A", "Dso::B"),
      ("Option<Int>", #[("opt", "other"), ("Option::Some(n)", "Option::Some(m)")], "Option::Some(_)", "Option::None"),
      ("Dsr", #[("tree", "branch"), ("Dsr::Next(tree)", "Dsr::Next(branch)")], "Dsr::End", "Dsr::Next(_)")]
    let (pat, otherPat) ← if pat == "Ds::A" then
      pick #[(pat, otherPat), ("Ds::A | Ds::B", "Ds::C(_)"),
        ("Ds::C(0..=2)", "Ds::C(3..=5)"), ("Ds::C(_)", "Ds::C(1)")]
    else if pat == "Dsr::End" then
      pick #[(pat, otherPat), ("Dsr::Next(Dsr::End)", "Dsr::Next(Dsr::Next(_))")]
    else if pat == "0..=2" then
      pick #[(pat, otherPat), ("0 | 2", "1 | 3"), ("0..=2", "2..=4")]
    else pure (pat, otherPat)
    let (x, y) ← pick pairs
    -- The same enclosing forms at every type, including generic and
    -- recursive enumerations. Parentheses keep open-ended operands local.
    let wrap ← below 6
    let localName := if ty == "Bool" then "ds_value?" else "ds_value"
    let otherLocal := if ty == "Bool" then "ds_other?" else "ds_other"
    -- `where` follows a whole body or constraint, never a scrutinee.
    let defs := if wrap == 3 then s!" where {localName} := ({x}), {otherLocal} := ({y})" else ""
    let enclose (x y : String) : String := match wrap with
      | 0 => x
      | 1 => s!"ds_id(({x}))"
      | 2 => s!"let {localName} := ({x}) in {localName}"
      | 3 => x
      | 4 => s!"if a? then ({x}) else ({y})"
      | _ => s!"match a? \{ true => ({x}), false => ({y}) }"
    let (x, y) := if wrap == 3 then (localName, otherLocal) else (enclose x y, enclose y x)
    let repeated ← chance 70
    let second := if repeated then x else y
    let bare := if second.all (fun c => c.isAlphanum || c == '_' || c == '?') then second else s!"({second})"
    let decorated ← pick #[bare, s!"({second})", s!"(/- column -/ {second})"]
    let third ← chance 40
    let scrs := s!"({x}), {decorated}" ++ (if third then s!", ({x})" else "")
    let tail := if third then ", _" else ""
    let guarded ← chance 40
    let guard := if guarded then " if a?" else ""
    let kw ← pick #["match", "table"]
    let e := s!"{kw} {scrs} \{ {pat}, {otherPat}{tail}{guard} => n + 1, _, _{tail} => m }"
    let bodies := #[e, s!"let result := {e} in result + 1", s!"({e}) + 1",
      s!"if ({e}) > n then n else m", s!"match ({e}) \{ 0 => n, _ => m }"]
    if (e ++ defs).contains "ds_unknown" then
      -- Uninterpreted applications belong in procedures, never in a
      -- defined function or a closure.
      let body ← pick bodies
      out := out ++ s!"pub proc ds_p{k}({params}): (value: Int) \{ ensure result: value = ({body}){defs} }\n"
    else
      let body ← pick (bodies.push s!"ds_apply(|arg| ({e}) + arg, n)")
      out := out ++ s!"pub fn ds_f{k}({params}): Int := {body}{defs}\n"
  -- Append after every existing draw, keeping each seed's earlier text.
  let (a, b) ← pick #[("n", "m"), ("m", "n")]
  let kw ← pick #["match", "table"]
  return out ++ s!"pub fn ds_groups(n: Int, m: Int): Int := {kw} {a}, {b}, {a}, {b} \{ 0, 0, 0, 1 => 1, 0, 1, 1, 1 => 2, _, _, _, _ => 0 }\n" ++
    s!"pub fn ds_generic<T>(o: Option<T>): Int := {kw} o, o \{ Option::Some(_), Option::None => 1, _, _ => 0 }\n"

end FrenTest.FuzzFrontends.Wide
