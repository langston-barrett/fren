import FrenCli.Search

/-! Short quantified global claims, with a generator independent of all
existing front-end modes. -/

namespace FrenTest.FuzzShortInduction

open FrenCli.Eval

private def pick (xs : Array α) [Inhabited α] : R α := do
  return xs[← below xs.size]!

/-- Short claims with leading binder groups, recursive lists, branching
trees, generic instances and subset payloads; companion types and parameter
order; comparisons, guards, definitions, Boolean blocks and shadowing.
All claims hold, including the forms whose unchanged candidate restrictions
leave them inconclusive. -/
def spec : R String := do
  let mut out := "mod short_induction\nset_option fren.lint.undecidable \"allow\"\n" ++
    "pub enum L { Z, S(Int, L) }\n" ++
    "pub enum T { Leaf, Node(T, Bool, T) }\n" ++
    "pub enum G<A> { Z, S(A, G<A>) }\n" ++
    "pub type Alias := L\n" ++
    "pub type Atom\n" ++
    "pub struct Record { value: Int }\n" ++
    "pub struct Wrap(Int)\n" ++
    "pub type Positive = n: Int where positive: n > 0\n" ++
    "pub enum PL { Z, S(Positive, PL) }\n" ++
    "pub fn plen(p: PL): Int := match p { PL::Z => 0, PL::S(_, t) => 1 + plen(t) }\n" ++
    "pub fn len(a: L): Int := match a { L::Z => 0, L::S(_, t) => 1 + len(t) }\n" ++
    "pub fn app(a: L, b: L): L := match a { L::Z => b, L::S(h, t) => L::S(h, app(t, b)) }\n" ++
    "pub fn nodes(t: T): Int := match t { T::Leaf => 0, T::Node(l, _, r) => 1 + nodes(l) + nodes(r) }\n" ++
    "pub fn count<A>(g: G<A>): Int := match g { G::Z => 0, G::S(_, t) => 1 + count(t) }\n" ++
    "pub fn keep<A>(x: A, a: L): A := match a { L::Z => x, L::S(_, t) => keep(x, t) }\n" ++
    "pub fn weight(L): Int\n" ++
    "pub fn generic_weight<A>(G<A>): Int\n"
  let binders ← pick #["(a b: L)", "(a: L) (b: L)", "(b: L) (a: Alias)"]
  let arg ← pick #["a", "((a))"]
  let rhs := s!"app({arg}, L::Z) = a"
  let body ← pick #[rhs, s!"not (app({arg}, L::Z) != a)",
    s!"when b = L::Z, len(app({arg}, b)) = len(a)",
    s!"let x := {arg} in app(x, L::Z) = x",
    s!"app(x, L::Z) = x where x := {arg}",
    s!"app({arg}, x) = a where x := L::Z",
    s!"and \{ right: {rhs}, nonnegative: len(a) >= 0 }",
    s!"or \{ right: {rhs}, nonnegative: len(a) >= 0 }",
    s!"iff \{ right: {rhs}, nonnegative: len(a) >= 0 }",
    s!"one \{ right: {rhs}, impossible: len(a) < 0 }",
    s!"({rhs}) iff true",
    s!"({rhs}) or len(a) >= 0",
    s!"if len(b) > 0 then {rhs} else len(a) >= 0",
    s!"(match b \{ L::Z => true, L::S(_, a!) => len(a) >= 0 }) and ({rhs})"]
  out := out ++ s!"expect list: forall {binders}, {body}\n"
  let ty ← pick #["Int", "Nat", "Bool", "String", "Atom", "Record", "Wrap", "Set<Int>", "Seq<Int>",
    "Rel<Int, Bool>", "Option<Int>", "Result<Int, Bool>", "G<G<Bool>>", "Positive", "Set<Positive>",
    "Seq<Positive>", "Rel<Positive, Int>", "Rel<Int, Positive>", "Option<Positive>", "Seq<Option<Positive>>"]
  let x := if ty == "Bool" then "x?" else "x"
  let binders ← pick #[s!"({x}: {ty}) (a: L)", s!"(a: L) ({x}: {ty})"]
  out := out ++ s!"expect companion: forall {binders}, app(a, L::Z) = a and keep({x}, a) = {x}\n"
  let op ← pick #[">=", ">", "!=", "<=", "<", "="]
  let expression := if op == "<=" || op == "<" then "-nodes(t)" else if op == "=" then "nodes(t) - nodes(t)" else "nodes(t)"
  let other := if op == ">" || op == "!=" then "-1" else if op == "<" then "1" else "0"
  out := out ++ s!"expect tree: forall (t: T), {expression} {op} {other}\n"
  if (← below 2) == 0 then
    out := out ++ "expect label_collision: forall (claim: L), app(claim, L::Z) = claim\n"
  let elem ← pick #["Int", "Bool", "String", "G<Int>",
    "Set<Int>", "Seq<Bool>", "Rel<Int, Bool>", "Option<Bool>", "Result<Int, String>"]
  out := out ++ s!"expect generic: forall (g: G<{elem}>), count(g) >= 0\n"
  out := out ++ "expect refined_payload: forall (p: PL), plen(p) >= 0\n"
  let excluded ← pick #["expect no_prefix: (forall (a: L), len(a) >= 0)",
    "expect constructed: forall (a: L), len(L::S(0, a)) > 0",
    "expect abstract: forall (a: L), len(a) + weight(a) >= weight(a)",
    "expect generic_abstract: forall (g: G<Int>), count(g) + generic_weight(g) >= generic_weight(g)",
    "expect nested: forall (a: L), forall (b: L), len(app(a, b)) >= len(a)",
    "expect shadow: forall (a b: L), match b { L::Z => true, L::S(_, a!) => len(a) >= 0 }"]
  return out ++ excluded ++ "\n"

end FrenTest.FuzzShortInduction
