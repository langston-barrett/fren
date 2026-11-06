-- keep-sorted start
import FrenTest.FuzzFrontends.Expressions
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- Generic functions whose type parameters are element types
(`lang::element_parameter`): sets, sequences and relations of them, nested
and within an instance, in signatures, bodies and contracts, defined and
not, one applied within another at its own type parameter, one whose type
argument only what is expected gives, one with a function parameter,
preconditions and postconditions over an element of a `Seq<T>`, and a
procedure that applies them at one element type: `Int`, `Bool`, `String`, an
abstract type, `E` if the spec has it, or `Option<Int>`, with arguments that
are empty literals, nested or not, in either order. Now and then, at `Bool`
or `E`, the procedure is enumerated, with only inputs of that type and small
sets and sequences of it, so that it is enumerated indeed. A postcondition
may fail, a check's result, but nothing here is a static error: no
relational operator or quantifier over a set's members, which are outside
the decidable core, and the function without a body only at `Int`, since one
of sets of a type that may be finite is too (#437). -/
def genericElements (sc : WScope) : R String := do
  let mut out := "pub type Atom\n" ++
    "pub fn ge_grow<T>(s: Set<T>, x: T): Set<T> := s union {x}\n" ++
    "pub fn ge_twice<T>(s: Set<T>, x: T): Set<T> := ge_grow(ge_grow(s, x), x)\n" ++
    "pub fn ge_has?<T>(s: Set<T>, x: T) := x in s\n" ++
    "pub fn ge_first<T>(q: Seq<T>, d: T): T := if q != [] then q[0] else d\n" ++
    "pub fn ge_at<T>(q: Seq<T>): T := q[0]\n" ++
    "pub fn ge_apply?<T>(q: Seq<T>, f: fn(T) -> Bool) := f(q[0])\n" ++
    "pub fn ge_pick<T>(q: Seq<T>, d: T): (r: T) {\n    require first: q[0] = d\n    out r := d\n    ensure same: r = q[0]\n}\n" ++
    "pub fn ge_head<T>(q: Seq<T>): (r: T) {\n    ensure m: r = q[0]\n}\n" ++
    "pub fn ge_len<T>(q: Seq<T>): Int := q.len\n" ++
    "pub fn ge_all?<T>(q: Seq<T>, s: Set<T>) := forall (x: T), when x in q, x in s\n" ++
    "pub fn ge_nest<T>(s: Set<Set<T>>, x: T): Set<Set<T>> := s union {{x}}\n" ++
    "pub fn ge_sets?<T>(q: Seq<Set<T>>, s: Set<T>) := q = [s]\n" ++
    "pub fn ge_deep<T>(q: Seq<Seq<T>>, d: T): T := if q = [] then d else q[0][0]\n" ++
    "pub fn ge_deep2<T>(d: T, q: Seq<Seq<T>>): T := if q = [] then d else q[0][0]\n" ++
    "pub fn ge_opt<T>(s: Set<T>): Option<Set<T>> := if s = {} then Option::None else Option::Some(s)\n" ++
    "pub fn ge_put<T>(q: Seq<Option<T>>, x: T): Seq<Option<T>> := q.update(0, Option::Some(x))\n" ++
    "pub fn ge_pair<A, B>(a: A, b: B): Rel<A, B> := {(a, b)}\n" ++
    "pub fn ge_in?<A, B>(r: Rel<A, B>, a: A, b: B) := (a, b) in r\n" ++
    "pub fn ge_parts<T>(s: Set<T>, t: Set<T>): Int := (s inter t).card + (s minus t).card\n"
  -- A contract over a set of the parameter, which holds or fails.
  let post ← pick #["not x in r", "r subset s", "r = s", "r.card < s.card"]
  out := out ++ s!"pub fn ge_drop<T>(s: Set<T>, x: T): (r: Set<T>) \{\n    out r := s minus \{x}\n    ensure q: {post}\n}\n"
  if ← chance 50 then
    out := out ++ "pub fn ge_choose<T>(s: Set<T>): (r: T) {\n    require ne: s != {}\n    ensure m: r in s\n}\n"
  -- The element type, and two of its values, distinct where it has two.
  let tys := #[("Int", "1", "2"), ("Bool", "true", "false"), ("String", "\"a\"", "\"b\""), ("Atom", "", ""),
    ("Option<Int>", "Option::None", "Option::Some(0)")] ++
    (if sc.nVariants > 0 then #[("E", "E::V0", "E::V1")] else #[])
  let (ty, a, b) ← pick tys
  -- Enumerated now and then, at a finite element type: then its inputs are
  -- only of that type, and the function without a body, whose
  -- postcondition blocks enumeration, is not applied.
  let enumerated := (ty == "Bool" || ty == "E") && (← chance 50)
  -- Its variables, named with `?` if they are `Bool`s.
  let x := if ty == "Bool" then "x?" else "x"
  let y := if ty == "Bool" then "y?" else "y"
  let lit (v : String) : R String := do if v.isEmpty then pure x else pick #[v, x, y]
  let n := if enumerated then "0" else "n"
  -- A value to compare with: not `q[0]` of a `Seq<String>`, which with an
  -- application is a comparison of two strings neither of which is a
  -- variable, outside the decidable core.
  let other : R String := if ty == "String" then pure x else pick #[x, "q[0]"]
  let mut body := ""
  for k in [0:(← below 4) + 2] do
    let e ← match ← below 19 with
      | 0 => pure s!"{x} in ge_grow(s, {x})"
      | 1 => pure s!"ge_has?(ge_grow(s, {← lit a}), {← lit b})"
      | 2 => pure s!"ge_first(q, {y}) = {← pick #[x, y]}"
      | 3 => pure s!"ge_all?(q, ge_grow(s, {← lit a}))"
      | 4 => pure s!"\{{x}} in ge_nest(\{s}, {← lit b})"
      | 5 => pure s!"(ge_opt(s) = Option::None) iff s = \{}"
      | 6 => pure s!"ge_put([Option::None], {x}) = [Option::Some({← lit a})]"
      | 7 => pure s!"ge_in?(ge_pair({x}, {← pick #["0", n]}), {← lit b}, {n})"
      | 8 => pure s!"ge_parts(s, \{{x}}) {← pick #["=", ">=", "<"]} s.card"
      | 9 => pure s!"not {x} in ge_drop(s, {← lit b})"
      | 10 => pure s!"ge_twice(s, {← lit a}) = ge_grow(s, {← lit b})"
      | 11 => pure s!"ge_len({← pick #["q", s!"[{x}]", s!"[{x}, {y}]"]}) > 1"
      | 12 =>
        -- Not both empty, which would leave `T` unknown (`F0400`).
        let q ← pick #["[s]", s!"[\{{x}}]", "[{}]"]
        pure s!"ge_sets?({q}, {← pick (if q == "[{}]" then #["s"] else #["s", "{}"])})"
      | 13 =>
        let q ← pick #["[[]]", s!"[[{x}]]", "[]", "[q]"]
        let call ← pick #[s!"ge_deep({q}, {y})", s!"ge_deep2({y}, {q})"]
        pure s!"{call} = {← if ← chance 33 then other else pick #[x, y]}"
      -- An instance whose type argument only what is expected gives.
      | 14 => pure s!"{← other} {← pick #["=", "!="]} ge_at([])"
      -- A generic function with a function parameter, given a closure or,
      -- at a type with a literal, a named function (`ge_is?`).
      | 15 =>
        let v := if ty == "Bool" then "v?" else "v"
        let f ← if a.isEmpty || (← chance 50) then pure s!"|{v}| {v} = {y}" else pure "ge_is?"
        pure s!"ge_apply?({← pick #["q", s!"[{x}]"]}, {f})"
      -- A precondition and a postcondition over an element of a `Seq<T>`,
      -- read at the instance, the function without a body's only where the
      -- procedure is not enumerated, as its postcondition blocks it.
      | 16 => pure s!"ge_pick({← pick #["q", s!"[{x}]", "[]"]}, {← pick #[y, "q[0]"]}) = {← other}"
      | 17 =>
        if enumerated then pure s!"{x} in ge_grow(s, {x})"
        else pure s!"ge_head({← pick #["q", s!"[{x}]"]}) {← pick #["=", "!="]} {← other}"
      | _ => pure s!"ge_first([{← lit a}], {y}) = {← lit b}"
    let e := if ← chance 30 then s!"when {x} != {y}, {e}" else e
    body := body ++ s!"    expect ge{k}: {e}\n"
  if out.contains "ge_choose" && !enumerated then
    body := body ++ s!"    expect gc: when ks != \{}, ge_choose(ks) in ks\n"
  let xs := if ty == "Bool" then s!"{x}, {y}" else s!"{x}: {ty}, {y}: {ty}"
  if body.contains "ge_is?" then
    out := out ++ (if ty == "Bool" then s!"pub fn ge_is?(v?) := v? = {a}\n" else s!"pub fn ge_is?(v: {ty}) := v = {a}\n")
  if enumerated then
    return out ++ "set_option fren.enumeration.size 2 in\nset_option fren.evidence \"enumerated\" in\n" ++
      s!"pub proc ge_apps({xs}, s: Set<{ty}>, q: Seq<{ty}>) \{\n{body}}\n"
  return out ++ s!"pub proc ge_apps({xs}, s: Set<{ty}>, q: Seq<{ty}>, n: Int, ks: Set<Int>) \{\n{body}}\n"

end FrenTest.FuzzFrontends.Wide
