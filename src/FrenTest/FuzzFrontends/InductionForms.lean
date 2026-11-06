-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- Global expectations in the forms where the two front ends read a
candidate for induction with code of their own (`lang::induction_candidate`,
`--induction-forms`): a decreasing argument in parentheses or nested in
another application; one hidden by a `match` arm's binder that shadows the
parameter; a recursion applied only to another expression; the other members
of a block (`let`, `use`, a call, a `cover`, a claim under an evidence
setting, an assumption that is a Boolean block); an uninterpreted
function, generic or not; a parameter of a type alias, of a nested instance
of a generic enumeration, and of an enumeration with a payload of a subset
type; and an enumeration of another module, which is not tried
(`Reqs/Lang/Recursion#induction`). Each claim holds, so no result depends
on a model. A mode of its own, so that no other seed's spec changes. -/
def inductionForms : R String := do
  let mut out := "mod jforms\n\npub enum JL { Nil, Cons(Int, JL) }\n" ++
    "pub enum JG<A> { Z, S(A, JG<A>) }\n" ++
    "pub type JList := JL\n" ++
    "pub type JPos = n: Int where positive: n >= 1\n" ++
    "set_option fren.lint.undecidable \"allow\" in\npub enum JP { Nil, Cons(JPos, JP) }\n" ++
    "pub fn jlen(l: JL): Int := match l { JL::Nil => 0, JL::Cons(_, r) => 1 + jlen(r) }\n" ++
    "pub fn japp(a: JL, b: JL): JL := match a {\n" ++
    "    JL::Nil => b,\n    JL::Cons(h, t) => JL::Cons(h, japp(t, b)),\n}\n" ++
    "pub fn jcount<A>(g: JG<A>): Int := match g { JG::Z => 0, JG::S(_, r) => 1 + jcount(r) }\n" ++
    "pub fn jplen(l: JP): Int := match l { JP::Nil => 0, JP::Cons(_, r) => 1 + jplen(r) }\n" ++
    "pub fn jw(JL): Int\n" ++
    "pub fn jgw<T>(T): Int\n" ++
    "pub proc jmeasure(l: JL): (det n: Int) {\n    ensure value: n = jlen(l)\n}\n"
  let adds (a b : String) := s!"jlen(japp({a}, {b})) = jlen({a}) + jlen({b})"
  -- Each form, with the parameters it is over and its block, drawn or not.
  let forms : Array (String × String × String) := #[
    ("parens", "a: JL, b: JL", s!"expect c: {adds "(a)" "b"}"),
    ("nested", "a: JL, b: JL, c: JL",
      "expect holds: jlen(japp(japp(a, b), c)) = jlen(a) + jlen(b) + jlen(c)"),
    ("shadowed", "a: JL, b: JL",
      "expect c: match b {\n        JL::Nil => jlen(a) >= 0,\n        JL::Cons(_, a!) => jlen(a) >= 0,\n    }"),
    ("other_arg", "a: JL", "expect c: jlen(JL::Cons(1, a)) >= 1"),
    ("let_member", "a: JL, b: JL", s!"let n: Int := jlen(a)\n    expect c: n + jlen(b) = jlen(a) + jlen(b)"),
    ("use_member", "a: JL", "use self::JL::{Nil}\n    expect c: japp(a, Nil) = a"),
    ("call_member", "a: JL, b: JL", "call m := jmeasure(japp(a, b))\n    expect c: m.n = jlen(a) + jlen(b)"),
    ("cover_member", "a: JL, b: JL", s!"cover nonempty: a != JL::Nil\n    expect c: {adds "a" "b"}"),
    ("evidence", "a: JL, b: JL", s!"set_option fren.evidence \"solver\" in\n    expect c: {adds "a" "b"}"),
    ("block_assume", "a: JL, b: JL",
      "assume e: and {\n        empty: b = JL::Nil,\n        zero: jlen(b) = 0,\n    }\n    expect c: jlen(japp(a, b)) = jlen(a)"),
    ("abstract", "a: JL, b: JL", s!"expect c: {adds "a" "b"} + jw(a) - jw(a)"),
    ("generic_abstract", "a: JL, b: JL", s!"expect c: {adds "a" "b"} + jgw(a) - jgw(a)"),
    ("alias", "a: JList, b: JL", s!"expect c: {adds "a" "b"}"),
    ("nested_instance", "g: JG<JG<Int>>", "expect c: jcount(g) >= 0"),
    ("subset_payload", "l: JP", "expect c: jplen(l) >= 0")]
  for (n, params, body) in forms do
    if ← chance 50 then out := out ++ s!"\nexpect jf_{n}({params}) \{\n    {body}\n}\n"
  -- An enumeration of another module, last, as its module's `use` ends
  -- the spec.
  if ← chance 30 then
    out := out ++ "\nmod jother\n\nuse jforms::{JL, japp, jlen}\n" ++
      s!"\nexpect jf_module(a: JL, b: JL) \{\n    expect c: {adds "a" "b"}\n}\n"
  return out

end FrenTest.FuzzFrontends.Wide
