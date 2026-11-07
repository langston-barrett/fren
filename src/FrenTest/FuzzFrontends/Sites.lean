-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- An expression of the collection type `ty` (`"Set<Int>"`, `"Rel<Int, Int>"`,
`"Seq<Int>"` or `"Option<Int>"`) that does not synthesize its type: its
empty value, `{}`, `[]` or `Option::None`, within parentheses,
conditionals, `match`es, tables, the bodies of `let`s, definitions whose
type is written, and `union`, or, seldom, `other`, a variable of the type,
which synthesizes it (`lang::synthesizes`). -/
partial def unsynthesized (ty : String) (other : String) (d : Nat) : R String := do
  let empty := if ty == "Seq<Int>" then "[]" else if ty == "Option<Int>" then "Option::None" else "{}"
  let sub := unsynthesized ty other (d - 1)
  if d == 0 || (← chance 35) then return if ← chance 10 then other else empty
  match ← below 8 with
  | 0 => return s!"({← sub})"
  | 1 => return s!"(if c? then {← sub} else {← sub})"
  | 2 => return s!"match o \{ Option::Some(_) => {← sub}, Option::None => {← sub} }"
  | 3 => return s!"table \{ c? => {← sub}, _ => {← sub} }"
  -- Named by depth, so that nothing shadows them.
  | 4 => return s!"(let t{d}: {ty} := {← sub} in t{d})"
  | 5 => return s!"(let t{d} := {other} in {← sub})"
  | _ =>
    if ty == "Set<Int>" || ty.startsWith "Rel" then return s!"({← sub} {← pick #["union", "inter", "minus"]} {← sub})"
    return s!"({← sub})"

/-- The declarations that the procedures of `sitesProc` use. -/
def sitesDecls : String :=
  "pub struct SiteRec { m: Set<Int>, n: Int }\n" ++
  "pub fn site_card(t: Set<Int>): Int := t.card\n" ++
  "pub fn site_first(t: Seq<Int>): Int := if t.len > 0 then t[0] else 0\n"

/-- A procedure `name` that writes expressions that do not synthesize their
types at each kind of site that `ExprSite` lists where they are checked
(`lang::checked`): beside a part that synthesizes one or none, as an
argument, a payload, a field of a record literal or update, a written
definition, the right of `in`, and the branches, arms and rows beside a
variable. Each is well typed and in the decidable core, so that it stops
none of the spec's other checks. With `unchecked`, it ends with one where
they are not checked, an error, reported alike, which stops them all, as in
`--sites` mode. -/
def sitesProc (name : String) (unchecked : Bool := false) : R String := do
  let set : R String := unsynthesized "Set<Int>" "s" 2
  let rel : R String := unsynthesized "Rel<Int, Int>" "r" 2
  let seq : R String := unsynthesized "Seq<Int>" "q" 2
  let opt : R String := unsynthesized "Option<Int>" "o" 2
  let mut body := ""
  for k in [0:(← below 5) + 2] do
    let e ← match ← below 19 with
      | 0 => pure s!"s = {← set}"
      | 1 => pure s!"{← set} = s"
      | 2 => pure s!"{← set} subset s"
      | 3 => pure s!"x in {← set}"
      | 4 => pure s!"site_card({← set}) >= 0"
      | 5 => pure s!"os != Option::Some({← set})"
      | 6 => pure s!"sr = SiteRec \{ m := {← set}, n := x }"
      | 7 => pure s!"sr = \{ sr with m := {← set} }"
      | 8 => pure s!"(let u: Set<Int> := {← set} in u subset s)"
      | 9 => pure s!"s = (s {← pick #["union", "inter", "minus"]} {← set})"
      | 10 => pure s!"s = (if c? then {← set} else s)"
      | 11 => pure s!"s = match o \{ Option::Some(_) => {← set}, Option::None => s }"
      | 12 => pure s!"s = table \{ c? => {← set}, _ => s }"
      | 13 => pure s!"(table \{ c? => {← set}, _ => s }).card >= 0"
      | 14 => pure s!"site_first({← seq}) = 0"
      | 15 => pure s!"o = {← opt}"
      | 16 => pure s!"{← opt} != o"
      | 17 => pure s!"(1, 2) in {← rel}"
      | _ => pure s!"r = (r union {← rel})"
    body := body ++ s!"    expect st{k}: {e}\n"
  if unchecked then
    let e ← match ← below 6 with
      | 0 => pure s!"({← set}).card = 0"
      | 1 => pure s!"r.image({← set}) = s"
      | 2 => pure s!"(let u := {← set} in u) = s"
      | 3 => pure s!"r = r join {← rel}"
      | 4 => pure s!"({← seq}).len = 0"
      | _ => pure s!"{← set} = {← set}"
    body := body ++ s!"    expect unchecked: {e}\n"
  return s!"pub proc {name}(s: Set<Int>, q: Seq<Int>, x: Int, c?, o: Option<Int>, os: Option<Set<Int>>, " ++
    s!"r: Rel<Int, Int>, sr: SiteRec) \{\n{body}}\n"

/-- A spec of `sitesProc`s alone, the last of which may write an expression
that does not synthesize its type where it is not checked (`--sites`). -/
def genSites : R String := do
  let mut out := "mod fz\n\n" ++ sitesDecls
  let n := (← below 2) + 1
  for i in [0:n] do
    out := out ++ (← sitesProc s!"sites{i}" (unchecked := i + 1 == n && (← chance 60)))
  return out

end FrenTest.FuzzFrontends.Wide
