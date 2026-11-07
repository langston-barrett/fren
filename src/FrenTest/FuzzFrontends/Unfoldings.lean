-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- Global expectations whose claims induction proves only by unfolding
more than one step of each function's equations, as the check of a function
generated for induction does (`Reqs/Lang/Recursion#unfolding-in-an-induction`):
over a list and a tree with two children and a `Bool` payload, claims whose
base case needs the equations at a depth that grows with a constant's size,
of 1 to 4 elements or levels, so that both sides of the bound are reached;
with another parameter now and then, in either order; and a claim with no
parameter, which no induction checks, and whose constant arguments need
the equations at depth 1. Other forms use generic lists, assumptions
and Boolean blocks, and a binary recursion whose deeper equations bring
another function's contract. Each claim holds, so no result depends on a
model. Its generator is split off the seed, so the other modes stay
unchanged. -/
def unfoldings : R String := do
  let mut out := "mod uunfold\n\n" ++
    "pub enum UL { Nil, Cons(Int, UL) }\n" ++
    "pub enum UT { Leaf(Bool), Node(UT, Int, UT) }\n" ++
    "pub fn ulen(l: UL): Int := match l { UL::Nil => 0, UL::Cons(_, r) => 1 + ulen(r) }\n" ++
    "pub fn uapp(a: UL, b: UL): UL := match a {\n" ++
    "    UL::Nil => b,\n    UL::Cons(h, t) => UL::Cons(h, uapp(t, b)),\n}\n" ++
    "pub fn uleaves(t: UT): Int := match t { UT::Leaf(_) => 1, UT::Node(l, _, r) => uleaves(l) + uleaves(r) }\n" ++
    "pub fn ugraft(t: UT, s: UT): UT := match t {\n" ++
    "    UT::Leaf(_) => s,\n    UT::Node(l, n, r) => UT::Node(ugraft(l, s), n, r),\n}\n"
  -- A list of `n` elements, and a tree of height `n` with `n + 1` leaves.
  let mut i := 0
  for n in [1, 2, 3, 4] do
    if ← chance 60 then
      let mut l := "UL::Nil"
      for _ in [0:n] do l := s!"UL::Cons({← below 10}, {l})"
      let mut t := s!"UT::Leaf({← pick #["true", "false"]})"
      for _ in [0:n] do t := s!"UT::Node(UT::Leaf({← pick #["true", "false"]}), {← below 10}, {t})"
      let extra ← chance 30
      let swap ← chance 50
      let ps (p : String) := if !extra then p else if swap then s!"k: Int, {p}" else s!"{p}, k: Int"
      let more := if extra then " + k - k" else ""
      if ← chance 70 then
        out := out ++ s!"\nexpect ul_{i}({ps "a: UL"}) \{\n    expect c: ulen(uapp(a, {l})) = ulen(a) + {n}{more}\n}\n"
      if ← chance 70 then
        out := out ++ s!"\nexpect ut_{i}({ps "t: UT"}) \{\n    expect c: uleaves(ugraft(t, {t})) = uleaves(t) + {n}{more}\n}\n"
    i := i + 1
  if ← chance 40 then
    out := out ++ s!"\nset_option fren.lint.assertions_on_constants \"allow\" in\nexpect uconst: ulen(uapp(UL::Nil, UL::Cons({← below 10}, UL::Nil))) = 1\n"
  out := out ++ "\npub enum UG<T> { Nil, Cons(T, UG<T>) }\n" ++
    "pub fn uglen<T>(l: UG<T>): Int := match l { UG::Nil => 0, UG::Cons(_, r) => 1 + uglen(r) }\n" ++
    "pub fn ugapp<T>(a: UG<T>, b: UG<T>): UG<T> := match a {\n" ++
    "    UG::Nil => b,\n    UG::Cons(h, t) => UG::Cons(h, ugapp(t, b)),\n}\n"
  let ty ← pick #["Int", "Bool"]
  let n := (← below 4) + 1
  let mut suffix := "UG::Nil"
  for _ in [0:n] do
    let value ← if ty == "Int" then toString <$> below 10 else pick #["true", "false"]
    suffix := s!"UG::Cons({value}, {suffix})"
  out := out ++ s!"\nexpect ug_assume(a: UG<{ty}>, b: UG<{ty}>) \{\n" ++
    s!"    assume fixed: b = {suffix}\n    expect c: uglen(ugapp(a, b)) = uglen(a) + {n}\n}\n" ++
    s!"\nexpect ug_block(a: UG<{ty}>) \{\n    expect c: and \{\n" ++
    s!"        length: uglen(ugapp(a, {suffix})) = uglen(a) + {n},\n" ++
    "        identity: ugapp(a, UG::Nil) = a,\n    }\n}\n"
  -- The two leaf applications are at depth 2; their equations introduce
  -- `uweight` at depth 3, where its contract still brings facts.
  out := out ++ "\npub fn uweight(t: UT): (n: Int) {\n    out n := match t {\n" ++
    "        UT::Leaf(_) => 1,\n        UT::Node(l, _, r) => uweight(l) + uweight(r),\n    }\n" ++
    "    ensure positive: n >= 1\n}\n" ++
    "pub fn ubranch(t: UT): Int := match t {\n" ++
    "    UT::Leaf(b?) => uweight(UT::Leaf(b?)),\n    UT::Node(l, _, r) => ubranch(l) + ubranch(r),\n}\n" ++
    "\nexpect ubinary(t: UT) {\n    expect c: ubranch(UT::Node(\n" ++
    s!"        UT::Node(UT::Leaf(true), {← below 10}, UT::Leaf(false)), {← below 10}, t\n" ++
    "    )) >= ubranch(t) + 2\n}\n"
  return out

end FrenTest.FuzzFrontends.Wide
