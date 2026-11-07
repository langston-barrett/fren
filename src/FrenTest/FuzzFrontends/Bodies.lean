-- keep-sorted start
import FrenTest.FuzzFrontends.Expressions
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- A body of type `t` where its type is expected, as a defined function's
body or a function block's `out` (`lang::checked`): the forms that take
their type from what is expected, `{}`, `[]` and a variant of the generic
`P<Int>` without a payload, within conditionals, `match`es, parentheses,
`union` and `++`, or any expression of the type. -/
partial def bodyOf (sc : WScope) (t : WTy) (genericPay : Bool) (d : Nat) : R String := do
  let sub := bodyOf sc t genericPay (d - 1)
  if d == 0 || (← chance 30) then
    match t with
    | .set => if ← chance 60 then return "{}" else return ← leaf sc .set
    | .rel => if ← chance 60 then return "{}" else return ← leaf sc .rel
    | .seq => if ← chance 60 then return "[]" else return ← leaf sc .seq
    | .pay => if genericPay && (← chance 60) then return "P::A" else return ← leaf sc .pay
    | _ => return ← gen sc t 1
  match ← below 6 with
  | 0 => return s!"if {← gen sc .bool 1} then {← sub} else {← sub}"
  | 1 =>
    if sc.nVariants == 0 then return s!"({← sub})"
    let arms ← (List.range sc.nVariants).toArray.mapM fun k => do return s!"E::V{k} => {← sub}"
    return s!"match {← gen sc .enum 0} \{ {", ".intercalate arms.toList} }"
  | 2 => return s!"({← sub})"
  | 3 => match t with
    | .set | .rel => return s!"{← sub} {← pick #["union", "inter", "minus"]} {← sub}"
    | .seq => return s!"{← sub} ++ {← sub}"
    | _ => sub
  | _ => gen sc t 2

/-- A body of type `Option<inner>`, where its type is expected:
`Option::None`, `Option::Some` of `inner`, or, seldom, of a `Bool`, a type
mismatch, within conditionals, `match`es and parentheses. -/
partial def optionBody (sc : WScope) (inner : R String) (d : Nat) : R String := do
  let sub := optionBody sc inner (d - 1)
  if d == 0 || (← chance 35) then
    match ← below 10 with
    -- A type mismatch, which `--avoid-known` leaves out: after it, the Lean
    -- front end may report a Lean error of its own too (#493).
    | 0 => return if sc.avoidKnown then "Option::None" else "Option::Some(true)"
    | 1 | 2 | 3 | 4 => return "Option::None"
    | _ => return s!"Option::Some({← inner})"
  match ← below 3 with
  | 0 => return s!"if {← gen sc .bool 1} then {← sub} else {← sub}"
  | 1 =>
    if sc.nVariants == 0 then return s!"({← sub})"
    let arms ← (List.range sc.nVariants).toArray.mapM fun k => do return s!"E::V{k} => {← sub}"
    return s!"match {← gen sc .enum 0} \{ {", ".intercalate arms.toList} }"
  | _ => return s!"({← sub})"

/-- A defined function `name` of the parameter `x0: Int` and result type
`ty` with the body `body`, written with `:=` or, sometimes, as a function
block whose `out` is the body. -/
def bodyFn (name ty body : String) (params := "x0: Int") (tps := "") : R String := do
  if ← chance 40 then return s!"pub fn {name}{tps}({params}): (r: {ty}) \{\n    out r := {body}\n}\n"
  return s!"pub fn {name}{tps}({params}): {ty} := {body}\n"

/-- Functions whose bodies are checked against their result types, of every
kind of result (`lang::checked`): collections, enumerations with payloads,
generic instances, aliases, subset types, a generic result, a structural
recursion, and now and then a body of another type. -/
def bodyFns (sc : WScope) (genericPay : Bool) : R String := do
  let sc := { sc with vars := #[("x0", WTy.int, true)] }
  let x : R String := gen sc .int 1
  let payTy := if genericPay then "P<Int>" else "P"
  let mut out := ""
  let mut aliases := false
  let mut subset := false
  let mut list := false
  for k in [0:(← below 4) + 1] do
    let name := s!"h{k}"
    match ← below 9 with
    | 0 | 1 | 2 =>
      let tys := #[(WTy.set, "Set<Int>"), (.seq, "Seq<Int>"), (.int, "Int"), (.rel, WTy.rel.name sc.relElem)] ++
        (if sc.hasPay then #[(WTy.pay, payTy)] else #[]) ++ (if sc.hasSeq then #[(WTy.bx, "Bx<Bx<Rq>>")] else #[])
      let (t, ty) ← pick tys
      -- Seldom a body of another type: a mismatch, reported alike.
      let bt ← if ← chance 8 then pick (tys.map (·.1)) else pure t
      out := out ++ (← bodyFn name ty (← bodyOf sc bt genericPay 3))
    | 3 => out := out ++ (← bodyFn name "Option<Int>" (← optionBody sc x 3))
    | 4 =>
      unless aliases do
        out := out ++ "pub type OptInt := Option<Int>\npub type IntSet := Set<Int>\n"
        aliases := true
      if ← chance 50 then out := out ++ (← bodyFn name "OptInt" (← optionBody sc x 3))
      else out := out ++ (← bodyFn name "IntSet" (← bodyOf sc .set genericPay 3))
    | 5 =>
      unless subset do
        out := out ++ "pub type Small = n: Int where small: n is 0..=5\n"
        subset := true
      if ← chance 50 then out := out ++ (← bodyFn name "Option<Small>" (← optionBody sc (pick #["0", "3", "9", "x0"]) 3))
      else out := out ++ (← bodyFn name "Small" (← pick #["3", "9", "x0", "if x0 > 0 then 1 else 7"]))
    | 6 | 7 =>
      -- A generic function, whose result mentions its type parameter.
      out := out ++ (← bodyFn s!"g{k}" "Option<T>" (← optionBody sc (pure "x") 3) (params := "x: T") (tps := "<T>"))
    | _ =>
      unless list do
        out := out ++ "pub enum L { Nil, Cons(Int, L) }\n"
        list := true
      let base ← pick #["Option::None", "Option::None", "Option::Some(0)"]
      out := out ++ s!"pub fn last{k}(l: L): Option<Int> := match l \{\n    L::Nil => {base},\n" ++
        s!"    L::Cons(h, t) => if t = L::Nil then Option::Some(h) else last{k}(t),\n}\n"
  return out

/-- Generic functions, and a procedure that applies them (`Reqs/Lang/GenericFunctions`):
`match`es that mention a value of the type parameter and that don't, a
generic enumeration's payload, and applications at `Int`, `Bool`, an
abstract type and a nested instance, with arguments whose type arguments
come from the expected type, as `Option::None`. -/
def genericApps (sc : WScope) (genericPay : Bool) : R String := do
  let mut out := "pub type Nm\n" ++
    "pub fn pick<T>(c?, a: T, b: T): T := if c? then a else b\n" ++
    "pub fn unwrap_or<T>(o: Option<T>, d: T): T := match o { Option::Some(x) => x, Option::None => d }\n" ++
    "pub fn some?<T>(o: Option<T>) := match o { Option::Some(_) => true, Option::None => false }\n" ++
    "pub fn wrap<T>(x: T): Option<T> := Option::Some(x)\n"
  if sc.hasPay && genericPay then
    out := out ++ "pub fn payload_or<X>(p: P<X>, d: X): X := match p { P::B(x) => x, _ => d }\n" ++
      "pub fn is_b?<X>(p: P<X>) := match p { P::B(_) => true, _ => false }\n"
  let isc : WScope := { sc with vars := #[("n", WTy.int, true), ("b?", .bool, true)], fns := #[] }
  -- Leaves, so that nothing here is an error of its own, such as a
  -- product of two variables, which would stop the spec's other checks.
  let int : R String := leaf isc .int
  let bool : R String := leaf isc .bool
  let mut body := ""
  for k in [0:(← below 4) + 2] do
    let e ← match ← below 10 with
      | 0 => pure s!"r = unwrap_or({← pick #["o", "Option::None", "wrap(n)", s!"Option::Some({← int})"]}, {← int})"
      | 1 => pure s!"s? = pick({← bool}, some?(o), {← bool})"
      | 2 => pure s!"t = pick({← bool}, m, m2)"
      | 3 => pure s!"u = unwrap_or(oo, {← pick #["Option::None", "o", "wrap(n)"]})"
      | 4 => pure s!"some?(oo) = some?({← pick #["o", "wrap(m)", "wrap(b?)", "wrap(oo)"]})"
      | 5 => pure s!"r = pick(some?(wrap({← bool})), {← int}, unwrap_or(unwrap_or(oo, o), n))"
      | 6 => pure s!"t = unwrap_or({← pick #["wrap(m)", "Option::None", "wrap(m2)"]}, m)"
      | 7 =>
        if sc.hasPay && genericPay then pure s!"r = payload_or({← pick #["P::A", "P::B(n)", "pp", "P::C(b?)"]}, {← int})"
        else pure s!"s? = some?(wrap({← bool}))"
      | 8 =>
        -- Not `P::A`, which leaves `X` unknown (`F0400`), an error.
        if sc.hasPay && genericPay then pure s!"s? = is_b?({← pick #["pp", "P::B(n)", "P::B(3)"]})"
        else pure s!"u = wrap({← int})"
      | _ => pure s!"t = pick({← bool}, m2, m)"
    body := body ++ s!"    ensure ga{k}: {e}\n"
  let pp := if sc.hasPay && genericPay then ", pp: P<Int>" else ""
  return out ++ s!"pub proc gapps(n: Int, b?, m: Nm, m2: Nm, o: Option<Int>, oo: Option<Option<Int>>{pp}): " ++
    s!"(r: Int, s?, t: Nm, u: Option<Int>) \{\n{body}}\n"

end FrenTest.FuzzFrontends.Wide
