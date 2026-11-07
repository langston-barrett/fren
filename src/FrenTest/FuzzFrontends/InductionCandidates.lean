-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- Specs of induction candidacy and function construction: each samples a
companion parameter type, an argument form and a comparison. Its generator
is split off the seed, leaving the other modes' draws unchanged. All claims
hold; no form adds a static error that suppresses the checks. -/
def inductionCandidates : R String := do
  let mut out := "mod kcandidates\n\nset_option fren.lint.undecidable \"allow\"\n\n" ++
    "pub enum KL { Nil, Cons(Int, KL) }\n" ++
    "pub enum KG<A> { Z, S(A, KG<A>) }\n" ++
    "pub enum KLeaf { A, B }\n" ++
    "pub enum KBox<A> { Box(A) }\n" ++
    "set_option fren.lint.non_camel_case_types \"allow\" in\npub enum KCollision { fren_induction_p0, C(Int, KCollision) }\n" ++
    "set_option fren.lint.non_camel_case_types \"allow\" in\npub enum fren_induction_p0 { Z, S(Int, fren_induction_p0) }\n" ++
    "pub type KAlias := fren_induction_p0\n" ++
    "pub struct KRecord { list: KL }\n" ++
    "pub struct KInt(Int)\n" ++
    "pub type KOpaque\n" ++
    "pub type KPos = n: Int where positive: n >= 1\n" ++
    "pub type KNonempty = l: KL where nonempty: l is KL::Cons(_, _)\n" ++
    "pub fn klen(l: KL): Int := match l { KL::Nil => 0, KL::Cons(_, r) => 1 + klen(r) }\n" ++
    "pub fn kapp(a: KL, b: KL): KL := match a {\n" ++
    "    KL::Nil => b,\n    KL::Cons(h, t) => KL::Cons(h, kapp(t, b)),\n}\n" ++
    "pub fn ksecond(k: Int, a: KL): KL := match a {\n" ++
    "    KL::Nil => KL::Nil,\n    KL::Cons(h, t) => KL::Cons(h, ksecond(k, t)),\n}\n" ++
    "pub fn kcount<A>(g: KG<A>): Int := match g { KG::Z => 0, KG::S(_, r) => 1 + kcount(r) }\n" ++
    "pub fn kkeep<A>(x: A, a: KL): A := match a { KL::Nil => x, KL::Cons(_, r) => kkeep(x, r) }\n" ++
    "pub fn kcollision(a: KCollision): Int := match a { KCollision::fren_induction_p0 => 0, KCollision::C(_, r) => 1 + kcollision(r) }\n" ++
    "pub fn kalias(a: KAlias): Int := match a { fren_induction_p0::Z => 0, fren_induction_p0::S(_, r) => 1 + kalias(r) }\n"
  let right := "kapp(a, KL::Nil) = a"
  -- Every unrestricted companion type must leave `a` a candidate; every
  -- restricted companion must exclude all parameters, even if unused.
  let types := #["Int", "Nat", "Bool", "String", "Set<Int>", "Seq<Int>", "Rel<Int, Bool>",
    "KLeaf", "KRecord", "KInt", "KOpaque", "KG<KG<Bool>>", "KNonempty", "KPos", "Set<KPos>",
    "Seq<KPos>", "Rel<KPos, Int>", "Rel<Int, KPos>", "KBox<KPos>", "KBox<Seq<KPos>>", "Seq<KBox<KPos>>"]
  let t ← pick types
  let x := if t == "Bool" then "x?" else "x"
  let ps := if ← chance 50 then s!"a: KL, {x}: {t}" else s!"{x}: {t}, a: KL"
  let same := if ← chance 50 then s!"kkeep({x}, a) = {x}" else s!"not (kkeep({x}, a) != {x})"
  out := out ++ s!"\nexpect kc_type({ps}) \{ expect c: ({right}) and ({same}) }\n"
  let forms : Array (String × String × String) := #[
    ("second", "k: Int, a: KL", "expect c: ksecond(k, a) = a"),
    ("second_parens", "a: KL, k: Int", "expect c: ksecond(k, ((a))) = a"),
    ("two", "b: KL, a: KL", "expect c: klen(kapp(a, b)) = klen(a) + klen(b)"),
    ("field", "r: KRecord", "expect c: klen(r.list) >= 0"),
    ("constructed", "a: KL", "expect c: klen(KL::Cons(0, a)) >= 1"),
    ("where", "a: KL", "expect c: kapp(t, KL::Nil) = t where t := a"),
    ("let_expr", "a: KL", "expect c: let t := a in kapp(t, KL::Nil) = t"),
    ("shadow_only", "a: KL, b: KL", "expect c: match b { KL::Nil => true, KL::Cons(_, a!) => klen(a) >= 0 }"),
    ("shadow_then_free", "a: KL, b: KL", s!"expect c: (match b \{ KL::Nil => true, KL::Cons(_, a!) => klen(a) >= 0 }) and ({right})"),
    ("nested_generic", "g: KG<KG<Bool>>", "expect c: kcount(g) >= 0"),
    ("nested_restricted", "a: KL, g: KBox<KBox<KPos>>", s!"expect c: {right}"),
    ("assumptions", "a: KL, b: KL", "assume one: b = KL::Nil\n    assume two: klen(b) = 0\n    expect c: klen(kapp(a, b)) = klen(a)"),
    ("bool_claims", "a: KL", s!"expect c: and \{ right: {right}, nonnegative: klen(a) >= 0 }"),
    ("conditional", "a: KL, b?", s!"expect c: if b? then {right} else klen(a) >= 0"),
    ("variant_placeholder", "a: KCollision", "expect c: kcollision(a) >= 0"),
    ("alias_placeholder", "a: KAlias", "expect c: kalias(a) >= 0")]
  let (n, ps, body) ← pick forms
  out := out ++ s!"\nexpect kc_{n}({ps}) \{\n    {body}\n}\n"
  -- Every comparison, with a recursive application nested in arithmetic.
  let op ← pick #["=", "!=", "<", "<=", ">", ">="]
  let rhs := if op == "!=" || op == "<" then "1" else if op == ">" then "-1" else "0"
  out := out ++ s!"\nexpect kc_compare(a: KL) \{ expect c: klen(a) - klen(a) {op} {rhs} }\n"
  return out

end FrenTest.FuzzFrontends.Wide
