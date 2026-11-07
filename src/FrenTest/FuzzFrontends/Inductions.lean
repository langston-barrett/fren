-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- Global expectations over recursive enumerations, whose claims their
checks leave Inconclusive and induction on a parameter may prove
(`Reqs/Lang/Recursion#induction`): over a list, a tree with two children
and a `Bool` payload, and an instance of a generic enumeration; with
parameters of those types, of `Int`, of `Bool` and of a payload's type,
in either order; under an assumption or not; claims that one step of each
function proves, that need more (which the deeper unfolding of an
induction's check may prove), and in a Boolean block; and the forms that
rule induction out: a call, an uninterpreted function, a parameter of a
subset type. Each claim holds, so no result depends on a model, but for
one false claim now and then, which fails under its function's contract
with a counterexample that evaluation does not confirm, not the internal
error of a model that contradicts Fren's semantics: so it stays
Inconclusive, with no model shown, induction is tried on it, and induction
must not pass it. It is written from a grammar of its own, as `factChain`
is. -/
def inductions : R String := do
  let mut out := "pub enum IdList { Nil, Cons(Int, IdList) }\n" ++
    "pub enum IdTree { Leaf(Bool), Node(IdTree, Int, IdTree) }\n" ++
    "pub enum IdGen<A> { Z, S(A, IdGen<A>) }\n" ++
    "pub fn idlen(l: IdList): Int := match l { IdList::Nil => 0, IdList::Cons(_, r) => 1 + idlen(r) }\n" ++
    "pub fn idapp(a: IdList, b: IdList): IdList := match a {\n" ++
    "    IdList::Nil => b,\n    IdList::Cons(h, t) => IdList::Cons(h, idapp(t, b)),\n}\n" ++
    "pub fn idsize(t: IdTree): Int := match t { IdTree::Leaf(_) => 1, IdTree::Node(l, _, r) => idsize(l) + 1 + idsize(r) }\n" ++
    "pub fn idmirror(t: IdTree): IdTree := match t {\n" ++
    "    IdTree::Leaf(x?) => IdTree::Leaf(x?),\n    IdTree::Node(l, n, r) => IdTree::Node(idmirror(r), n, idmirror(l)),\n}\n" ++
    "pub fn idcount<A>(g: IdGen<A>): Int := match g { IdGen::Z => 0, IdGen::S(_, r) => 1 + idcount(r) }\n"
  -- Each claim, with its parameters, which come in either order.
  let swap ← chance 50
  let two (x y : String) : String := if swap then s!"{y}, {x}" else s!"{x}, {y}"
  let claims : Array (String × String × String) := #[
    ("adds", two "a: IdList" "b: IdList", "expect c: idlen(idapp(a, b)) = idlen(a) + idlen(b)"),
    ("nil_right", "a: IdList", "expect c: idapp(a, IdList::Nil) = a"),
    ("assoc", "a: IdList, b: IdList, c: IdList", "expect holds: idapp(idapp(a, b), c) = idapp(a, idapp(b, c))"),
    ("mirror_size", "t: IdTree", "expect c: idsize(idmirror(t)) = idsize(t)"),
    ("mirror_twice", "t: IdTree", "expect c: idmirror(idmirror(t)) = t"),
    ("count", "g: IdGen<Int>", "expect c: idcount(g) >= 0"),
    ("suffix", two "a: IdList" "b: IdList", "assume e: b = IdList::Nil\n    expect c: idlen(idapp(a, b)) = idlen(a)"),
    ("one_more", two "a: IdList" "k: Int", "expect c: idlen(idapp(a, IdList::Cons(k, IdList::Nil))) = idlen(a) + 1"),
    ("flagged", two "a: IdList" "x?", "expect c: when x?, idapp(a, IdList::Nil) = a"),
    ("both", two "a: IdList" "b: IdList",
      "expect c: and {\n        n: idapp(a, IdList::Nil) = a,\n        s: idlen(idapp(a, b)) = idlen(a) + idlen(b),\n    }")]
  for (n, params, body) in claims do
    if ← chance 50 then out := out ++ s!"\nexpect id_{n}({params}) \{\n    {body}\n}\n"
  -- The forms that rule induction out.
  if ← chance 40 then
    out := out ++ "\npub proc idmeasure(l: IdList): (det n: Int) {\n    ensure value: n = idlen(l)\n}\n" ++
      "\nexpect id_called(a: IdList, b: IdList) {\n    call m := idmeasure(idapp(a, b))\n" ++
      "    expect c: m.n = idlen(a) + idlen(b)\n}\n"
  if ← chance 40 then
    out := out ++ "\npub fn idweight(IdList): Int\n" ++
      "\nexpect id_weighed(a: IdList, b: IdList) {\n    expect c: idlen(idapp(a, b)) + idweight(a) = idlen(a) + idlen(b) + idweight(a)\n}\n"
  if ← chance 40 then
    out := out ++ "\npub type IdCons = l: IdList where invariant: l is IdList::Cons(_, _)\n" ++
      s!"\nexpect id_subset({two "a: IdList" "b: IdCons"}) \{\n    expect c: idlen(idapp(a, b)) = idlen(a) + idlen(b)\n}\n"
  -- A false claim that its own check leaves Inconclusive, which induction
  -- must not pass, last.
  if ← chance 30 then
    out := out ++ "\nexpect id_off(a: IdList) {\n    expect c: idlen(a) != 5\n}\n"
  return out

end FrenTest.FuzzFrontends.Wide
