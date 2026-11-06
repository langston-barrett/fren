-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- A goal with leading binders (`cli::goal_introduction`), whose terms
mention `outer`, its body the first of them: one to three heads, each a universal quantifier over one
or two bound names, of an infinite type, `Nat`, an abstract type, or a
listed type, or a premise, in any order, then a body, and now and then a
guard within the last quantifier. -/
def goalWithHeads (outer : Array String) (tys : Array String := #["Int", "Nat", "Zgt", "Zgt", "Zge", "Bool"]) :
    R String := do
  let mut bound : Array (String × String) := #[]
  let mut heads : Array String := #[]
  -- An `Int` term of one of the names in scope.
  let intOf (scope : Array (String × String)) : R String := do
    if scope.isEmpty || (← chance 20) then return ← pick (outer.push "1")
    let (x, t) ← pick scope
    return match t with
      | "Zgt" => s!"zgw({x})"
      | "Self" => s!"zgo({x})"
      | "Zge" => s!"(if {x} = Zge::A then 1 else 0)"
      | "Bool" => s!"(if {x} then 1 else 0)"
      | _ => x
  let cond (scope : Array (String × String)) : R String := do
    match ← below 3 with
    | 0 =>
      match scope.find? (·.2 == "Zgt") with
      | some (x, _) => return s!"zgh?({x})"
      | none => match scope.find? (·.2 == "Self") with
        | some (x, _) => return s!"zgo({x}) > 0"
        | none => return s!"{← intOf scope} > 0"
    | 1 => return s!"{← intOf scope} {← pick #["<", "<=", "="]} {← intOf scope}"
    | _ => return s!"{← intOf scope} >= {← below 3}"
  for _ in [0:(← below 3) + 1] do
    if ← chance 60 then
      let mut names := #[]
      for _ in [0:(← below 2) + 1] do
        let t ← pick tys
        let x := if t == "Bool" then s!"zb{bound.size}?" else s!"zx{bound.size}"
        bound := bound.push (x, t)
        names := names.push s!"({x}: {t})"
      heads := heads.push s!"forall {" ".intercalate names.toList}, "
    else heads := heads.push s!"when {← cond bound}, "
  let guard ← if ← chance 30 then pure s!"when {← cond bound}, " else pure ""
  -- The right operand is the first of `outer`, if any, so that the
  -- goal mentions it, and an assumption over it is used (F0792).
  let rhs ← match outer[0]? with
    | some o => pure o
    | none => intOf bound
  let body := s!"{guard}{← intOf bound} {← pick #["<", "<=", ">=", "!="]} {rhs} + {← below 3}"
  -- Each head wraps the rest; a quantifier after a premise in parentheses.
  return heads.foldr (init := body) fun h rest =>
    if h.startsWith "when" && rest.startsWith "forall" then s!"{h}({rest})" else h ++ rest

/-- Goals with leading binders (`goalWithHeads`), as each item poses
them: a global expectation of each form, one with a quantified assumption
that only instances at the goal's bound names decide, as a trait's laws
are, a procedure with a defined output, which the binary's goal binds
with a `let`, a `let` and a `where` in front of a goal, and a trait's
expectations over `Self` under its laws (`Reqs/Cli#goal-introduction`). -/
def goalHeads : R String := do
  let mut out := "pub type Zgt\npub enum Zge { A, B }\npub fn zgw(Zgt): Int\npub fn zgh?(Zgt)\n"
  let undecidable := "set_option fren.lint.undecidable \"allow\" in\n"
  for k in [0:← below 2] do
    out := out ++ s!"\n{undecidable}expect zgs{k}: {← goalWithHeads #[]}\n"
  if ← chance 70 then
    let law ← pick #["zgw(zy) >= n", "zgw(zy) = n", "when zgh?(zy), zgw(zy) > n", "zgh?(zy)"]
    out := out ++ s!"\n{undecidable}expect zgl(n: Int) \{\n    assume a: forall (zy: Zgt), {law}\n" ++
      s!"    expect c: {← goalWithHeads #["n"]}\n}\n"
  if ← chance 70 then
    let mut body := "    out zd := n + 1\n"
    for k in [0:(← below 2) + 1] do
      body := body ++ s!"    expect c{k}: {← goalWithHeads #["n", "zd"]}\n"
    out := out ++ s!"\n{undecidable}pub proc zgp(n: Int): (zd: Int) \{\n{body}}\n"
  -- Drawn after the items above, so that they are as they were: a `let`
  -- or `where` in front of a goal, and a trait whose expectations
  -- quantify over `Self` under its laws, two of which may contradict each
  -- other, as at #543.
  if ← chance 60 then
    let goal ← goalWithHeads #["zl", "n"]
    let d ← below 3
    let e := if ← chance 50 then s!"let zl := n + {d} in {goal}" else s!"{goal} where zl := n + {d}"
    out := out ++ s!"\n{undecidable}pub proc zgq(n: Int) \{\n    expect c: {e}\n}\n"
  if ← chance 60 then
    let mut body := "    fn zgo(Self): Int\n"
    body := body ++ s!"    law zl0(s: Self): zgo(s) {← pick #["=", ">=", "<="]} {← below 4}\n"
    if ← chance 50 then body := body ++ s!"    law zl1(s: Self): zgo(s) = {← below 4}\n"
    for k in [0:(← below 2) + 1] do
      body := body ++ s!"    expect ze{k}: {← goalWithHeads #[] #["Self", "Self", "Int", "Nat"]}\n"
    out := out ++ s!"\n{undecidable}pub trait Zgr \{\n{body}}\n"
  return out

end FrenTest.FuzzFrontends.Wide
