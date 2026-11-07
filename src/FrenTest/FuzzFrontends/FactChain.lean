-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- A chain of uninterpreted functions with contracts, each of whose
postconditions applies the one before it, and checks over the last, so
that the facts of an application mention another, whose facts a query has
too, transitively (`check::fact_applications`, #619). Each link applies
the one before it in one of the forms that a fact's applications take: a
sum, a bound, a product, a conditional, a nested application of an
uninterpreted function without a contract, a quantifier whose body applies
a function into `Nat` at its bound name, an arm of a `match` that binds a
payload, a `where` clause, a table, a function into `Nat` or into a subset
type, without a contract, a generic function with a contract over the
first of the chain, and a recursive defined function with a
postcondition, whose defining equations a query reflects from a fact
(`lang::recursion_formulas`); its results `Int` or `Nat`, sometimes under
a precondition. An expectation and a cover goal over the last then hold or
fail by the facts of all of them, as do the rows of a table over the last
in a contract of its own, whose own facts its checks never have; and an
input, an output and a call's output of a subset type whose invariant
applies the recursive function. It is
appended to specs of the corpus, so it is written from a grammar of its
own, every form of which is well-typed, whatever the spec declares. -/
def factChain : R String := do
  let mut out := "pub type Fc\npub fn fct(Fc): Fc\n"
  let n := (← below 3) + 1
  let bound ← below 3
  let nat0 ← chance 30
  out := out ++ s!"pub fn fc0(s: Fc): (r: {if nat0 then "Nat" else "Int"}) \{ ensure e: r >= {bound} }\n"
  -- What the links may apply besides the chain, each well-typed alone.
  out := out ++ "pub enum Fk { A, B(Int) }\npub fn fck(Fc): Fk\npub fn fcn(Fc): Nat\npub fn fci(Int): Nat\n" ++
    "pub type FcPos = p: Int where invariant: p > 0\npub fn fcp(Fc): FcPos\n" ++
    "pub fn fcg<T>(x: T, y: T, s: Fc): (r: Int) { ensure e: r >= (if x = y then fc0(s) else fc0(s) + 1) }\n" ++
    "pub enum Fl { Nil, Cons(Int, Fl) }\npub fn fcl(Fc): Fl\n" ++
    "pub fn fcsum(l: Fl): (r: Int) {\n    out r := match l { Fl::Nil => 0, Fl::Cons(m, rest) => m.abs + fcsum(rest) }\n" ++
    "    ensure e: r >= 0\n}\n"
  for k in [1:n + 1] do
    let prev := s!"fc{k - 1}"
    let arg ← pick #["s", "fct(s)", "fct(fct(s))"]
    let app := if k == 1 then s!"{prev}({arg})" else s!"{prev}({arg}, b?)"
    let c ← below 3
    let form ← below 13
    let (opt, post) ← match form with
      | 0 => pure ("", s!"ensure e: r = {app} + {c}")
      | 1 => pure ("", s!"ensure e: r >= {app}")
      | 2 => pure ("", s!"ensure e: r > 2 * {app}")
      | 3 => pure ("", s!"ensure e: r = if b? then {app} else {c}")
      | 4 => pure ("", s!"ensure e: r = {app} - {c}")
      | 5 => pure ("set_option fren.lint.undecidable \"allow\" in\n",
          s!"ensure e: forall (i: Int), when 0 <= i < {c + 1}, r >= {app} + fci(i)")
      | 6 => pure ("", s!"ensure e: r = match fck(s) \{ Fk::A => {app}, Fk::B(x) => {app} + x.abs }")
      | 7 => pure ("", s!"ensure e: r = y + {c} where y := {app}")
      | 8 => pure ("", s!"ensure e: table \{ b? => r >= {app}, _ => r = {app} + {c} }")
      | 9 => pure ("", s!"ensure e: r = {app} + fcn({arg})")
      | 10 => pure ("", s!"ensure e: r = {app} + fcp({arg})")
      | 11 => pure ("", s!"ensure e: r = fcg(b?, true, {arg}) + {app}")
      | _ => pure ("", s!"ensure e: r = fcsum(Fl::Cons({c}, fcl({arg}))) + {app}")
    let pre := if ← chance 30 then s!"    require p: b?\n" else ""
    -- A `Nat` result only where the clause gives its value: where it only
    -- bounds it by an `Int`, Lean's realizability query often times out
    -- (#493).
    let ty := if k > 1 && [0, 7, 9, 10].contains form && (← chance 40) then "Nat" else "Int"
    out := out ++ s!"{opt}pub fn fc{k}(s: Fc, b?): (r: {ty}) \{\n{pre}    {post}\n}\n"
  -- Whatever its preconditions, `b?` is `true` at the checks, so that
  -- none fails at a call.
  let last := s!"fc{n}(s, true)"
  let c ← below 4
  out := out ++ s!"\nexpect fc_holds(s: Fc) \{ expect c: {last} >= {c} }\n"
  out := out ++ s!"\nproc fc_cover(s: Fc) \{\n    cover low: {last} < {c}\n}\n"
  if ← chance 40 then
    out := out ++ s!"\npub fn fc_table(s: Fc): (r: Int) \{\n    ensure t: table \{ fc{n}(s, true) >= {c} => r > 0, r < 0 => true, _ => true }\n}\n"
  -- An input, an output and a call's output of a subset type whose
  -- invariant applies the recursive `fcsum`, whose facts each query has
  -- (`lang::recursion_formulas`); its second row keeps the type inhabited
  -- without the opaque `fcsum`.
  if ← chance 50 then
    let b ← below 4
    let d ← below 4
    out := out ++ s!"\npub type FcBig = m: Int where invariant: fcsum(Fl::Cons(m, Fl::Nil)) >= {b} or m = {b}\n" ++
      "proc fc_in(x: FcBig): (det z: Int) { out z := x + 1 }\n" ++
      s!"proc fc_out(): (y: FcBig) \{\n    cover w: y = {d}\n}\n" ++
      s!"proc fc_call(u: Int) \{\n    call w := fc_out()\n    cover v: w.y = {d} + u\n}\n" ++
      s!"proc fc_in2(x: FcBig) \{\n    cover v: x > {d}\n}\n"
  return out

end FrenTest.FuzzFrontends.Wide
