-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- The literal `k` at the count type `ty`: an integer, or wrapped in each
newtype that `ty` is over, as `Cm3(Cm2(Cm(k)))` (`countDecls`). -/
def wrapLit (ty : String) (k : Nat) : String :=
  if ty == "Ms" then s!"Ms({k})"
  else if ty.startsWith "Cm" || ty.startsWith "Cn" then
    let base := (ty.take 2).toString
    let d := ((ty.drop 2).toString.toNat?).getD 1
    (List.range d).foldl (init := toString k) fun acc i =>
      s!"{base}{if i == 0 then "" else toString (i + 1)}({acc})"
  else toString k

/-- The indicator function at the count type `ty`, which `countDecls`
declares. -/
def countFn : String → String
  | "Int" => "ind" | "Nat" => "indn" | "Ms" => "indm" | t => "ind" ++ t.toLower

/-- A sum of a count's terms at the type `ty`, `Int`, `Nat` or a newtype over them: an
`if c then 1 else 0`, a literal, a constant, an application of the
type's indicator function, or one of `defs`, defined variables of the
type, which makes chains of definitions; `cond` gives each condition. -/
def countSum (ty : String) (defs : Array String) (cond : R String) : R String := do
  let lit := wrapLit ty
  let mut terms := #[]
  for _ in [0:(← below 3) + 1] do
    let t ← match ← below 6 with
      | 0 | 1 => pure s!"(if {← cond} then {lit 1} else {lit 0})"
      | 2 => pure (lit (← below 3))
      | 3 => match ty with
        | "Int" => pick #["ONE_I", "TWO_I"]
        | "Nat" => pick #["ONE_N", "TWO_N"]
        | _ => pure (lit 2)
      | 4 => pure s!"{countFn ty}({← cond})"
      | _ => if defs.isEmpty then pure s!"(if {← cond} then {lit 1} else {lit 0})" else pick defs
    terms := terms.push t
  return " + ".intercalate terms.toList

/-- What a count of `ty` is compared with: 1, or a constant that is 1. -/
def countOne (ty : String) : R String := match ty with
  | "Int" => pick #["1", "1", "ONE_I"]
  | "Nat" => pick #["1", "1", "ONE_N"]
  | t => pure (wrapLit t 1)

/-- A comparison of `lhs`, a count of `ty`, with 1, each way, sometimes
negated. -/
def countCmp (ty lhs : String) : R String := do
  let one ← countOne ty
  let cmp ← match ← below 7 with
    | 0 | 1 => pure s!"{lhs} <= {one}"
    | 2 | 3 => pure s!"{lhs} = {one}"
    | 4 => pure s!"{one} >= {lhs}"
    | 5 => pure s!"{lhs} < {one}"
    | _ => pure s!"{lhs} != {one}"
  return if ← chance 40 then s!"not ({cmp})" else cmp

/-- The declarations that counts use, and the newtypes among the count
types: an indicator function at `Int` and `Nat`, constants, and newtypes
over `Int` and `Nat`, each of a newtype over the one before to a random
depth, `Cm`, `Cm2(Cm)`, `Cm3(Cm2)` over `Int` and `Cn`, `Cn2(Cn)` over
`Nat`, with an indicator function each. -/
def countDecls : R (String × Array String) := do
  let mut out := "pub fn ind(c?): Int := if c? then 1 else 0\npub fn indn(c?): Nat := if c? then 1 else 0\n" ++
    "pub const ONE_I: Int := 1\npub const TWO_I: Int := 2\npub const ONE_N: Nat := 1\npub const TWO_N: Nat := 2\n"
  let mut tys := #[]
  for (base, under, top) in [("Cm", "Int", 3), ("Cn", "Nat", 2)] do
    let depth := (← below top) + 1
    for i in [1:depth + 1] do
      let ty := if i == 1 then base else s!"{base}{i}"
      let inner := if i == 1 then under else if i == 2 then base else s!"{base}{i - 1}"
      out := out ++ s!"pub ordered struct {ty}({inner})\n"
      out := out ++ s!"pub fn {countFn ty}(c?): {ty} := if c? then {wrapLit ty 1} else {wrapLit ty 0}\n"
      tys := tys.push ty
  return (out, tys)

/-- A procedure of counts alone, always enumerated, so that nothing else
about it hides how a front end reads them: over sequences whose indexes
may be out of range, with counts at every numeric type (`Int`, `Nat`, the
newtypes `newtypes` over them, and `Ms` if `hasMs`), each through defined
outputs, `let`s, functions and chains of them, or inline. -/
def countsProc (name : String) (hasMs : Bool) (newtypes : Array String) : R String := do
  -- At size 3, one sequence only, so that the procedure stays within the
  -- limit of behaviours (two `Seq<Int>` there have 160,000 assignments).
  let size := if ← chance 30 then 3 else 2
  let cond : R String := do
    match ← below 5 with
    | 0 | 1 => return s!"q[{← below 6}] > 0"
    | 2 => if size == 2 then return s!"r[{← below 6}] = {← below 2}" else return s!"q[{← below 6}] = {← below 2}"
    | 3 => pick #["b?", "not b?", "n > 0"]
    | _ => pick #["true", "false"]
  let tys := #["Int", "Nat"] ++ newtypes ++ (if hasMs then #["Ms"] else #[])
  let mut results := ""
  let mut body := ""
  let mut cvars : Array (String × String) := #[]
  for k in [0:← below 5] do
    let ty ← pick tys
    let e ← countSum ty (cvars.filterMap fun (n, t) => if t == ty then some n else none) cond
    let n := s!"k{k}"
    if ← chance 30 then body := body ++ s!"    let {n}: {ty} := {e}\n"
    else
      results := results ++ s!"    {n}: {ty},\n"
      body := body ++ s!"    out {n} := {e}\n"
    cvars := cvars.push (n, ty)
  for k in [0:(← below 4) + 1] do
    let ty ← pick tys
    let own := cvars.filterMap fun (n, t) => if t == ty then some n else none
    let lhs ← if !own.isEmpty && (← chance 60) then pick own else countSum ty own cond
    body := body ++ s!"    expect e{k}: {← countCmp ty lhs}\n"
  let resultList := if results.isEmpty then "" else s!": (\n{results})"
  let params := if size == 2 then "q: Seq<Int>, r: Seq<Int>, b?, n: Int" else "q: Seq<Int>, b?, n: Int"
  return s!"\nset_option fren.lint.undecidable \"allow\" in\nset_option fren.enumeration.size {size} in\n" ++
    s!"set_option fren.evidence \"enumerated\" in\npub proc {name}({params}){resultList} \{\n{body}}\n"

end FrenTest.FuzzFrontends.Wide
