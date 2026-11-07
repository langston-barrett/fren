-- keep-sorted start
import FrenTest.FuzzFrontends.Expressions
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- An uninterpreted function `name` whose postconditions are tables, each
row's condition a leaf (its parameter `x1?`, a `Bool` constant, `true` or
`false`), or a comparison of its value `r` or of `x0` with an `Int` leaf:
so that rows `K0` and `true` meet, and rows over `r` overlap where only
the clause that they are in rules it out (#559). The checks of its rows
ask about them without that clause, of `r`, not of the function's
application (`Reqs/Check#contracts-of-uninterpreted-functions`). It is
appended to specs of the corpus, so it is written from a grammar of its
own, every form of which is well-typed, whatever the spec declares: no
payload of a generic `P`, no ill-typed count, and no comparison of a name
with itself, which a lint reports. -/
def contractTable (sc : WScope) (name : String) : R String := do
  let bools := sc.constsOf .bool
  let ints := sc.constsOf .int
  -- An `Int` other than `r` and `x0`, which the comparisons have.
  let int : R String := do
    if !ints.isEmpty && (← chance 40) then pick ints else return toString (← below 4)
  let bool : R String := do
    match ← below 3 with
    | 0 => pure "x1?"
    | 1 => if bools.isEmpty then pick #["true", "false"] else pick bools
    | _ => pick #["true", "false"]
  let row : R String := do
    match ← below 3 with
    | 0 => bool
    | 1 => return s!"r {← pick #["=", "<", ">=", ">"]} {← if ← chance 30 then pure "x0" else int}"
    | _ => return s!"x0 {← pick #["=", "<", ">"]} {← int}"
  let value : R String := do
    if ← chance 50 then bool else return s!"r {← pick #["=", "<", ">"]} {← int}"
  let mut clauses := ""
  for j in [0:(← below 2) + 1] do
    let mut rows := #[]
    for _ in [0:(← below 3) + 2] do rows := rows.push s!"{← row} => {← value}"
    if ← chance 40 then rows := rows.push s!"_ => {← value}"
    clauses := clauses ++ s!"    ensure t{j}: table \{ {", ".intercalate rows.toList} }\n"
  return s!"pub fn {name}(x0: Int, x1?): (r: Int) \{\n{clauses}}\n"

/-- Uninterpreted functions with contracts of each form, applied by an
enumerated procedure (`check::contract_blocks_enumeration`): preconditions
alone, which do not keep it from being enumerated, postconditions alone,
both, or no contract. They are declared in an order of their own, and
applied in another, so that the function that `F0645` names, the first by
path of those with postconditions, is neither the first declared nor the
first applied. -/
def enumContracts (name : String) : R String := do
  let mut names := #["kca", "kcb", "kcc"]
  let mut decls := ""
  -- The names in a random order, each with a contract of a random form.
  for _ in [0:3] do
    let i ← below names.size
    let f := names[i]!
    names := names.eraseIdx! i
    let pre := s!"    require p: x >= {← pick #["-2", "-1", "0"]}\n"
    let post := s!"    ensure q: r > {← pick #["x", "x - 1"]}\n"
    let decl ← match ← below 4 with
      | 0 => pure s!"pub fn {f}(x: Int): (r: Int) \{\n{pre}}\n"
      | 1 => pure s!"pub fn {f}(x: Int): (r: Int) \{\n{post}}\n"
      | 2 => pure s!"pub fn {f}(x: Int): (r: Int) \{\n{pre}{post}}\n"
      | _ => pure s!"pub fn {f}(Int): Int\n"
    decls := decls ++ decl
  let mut apps := #[]
  let mut left := #["kca", "kcb", "kcc"]
  for _ in [0:3] do
    let i ← below left.size
    apps := apps.push s!"{left[i]!}(x)"
    left := left.eraseIdx! i
  let sum := " + ".intercalate apps.toList
  let options := "set_option fren.enumeration.size 2 in\nset_option fren.evidence \"enumerated\" in\n"
  return decls ++ s!"\n{options}pub proc {name}(x: Int): (det y: Int) \{\n    require a: x != 5\n    \
    out y := {sum}\n    expect e: y != {← below 3}\n}\n"

/-- Procedures checked by the solver whose outputs have subset types: of
`Int`, a subset of a subset, a record with a field of one, and a subset of
that record; each output `pub` or not (`exists`), `det` or not, with
guarantees that sometimes force a value outside its type, so that
realizability's `∃` over the outputs ranges over their types alone
(`Reqs/Models#what-is-not-confirmed`). It adds no static error. -/
def subsetOutputs : R String := do
  let bound := (← below 4) + 2
  let mut out := "pub type Sp = n: Int where pos: n > 0\n" ++
    s!"pub type Ss = s: Sp where small: s < {bound}\n" ++
    "pub struct Sbox { v: Ss, w: Int }\n" ++
    "pub type Sr = r: Sbox where ok: r.w >= 0\n"
  -- An integer from the inputs `x` and `y`.
  let int : R String := do
    match ← below 5 with
    | 0 => return "x"
    | 1 => return "y"
    | 2 => return s!"x + {← below 4}"
    | 3 => return s!"y - {← below 3}"
    | _ => return s!"{← below 5}"
  for c in [0:(← below 2) + 1] do
    let mut results := #[]
    let mut body := ""
    if ← chance 40 then body := body ++ s!"    require a: x > {← below 4}\n"
    for k in [0:(← below 2) + 1] do
      let ty ← pick #["Sp", "Ss", "Sbox", "Sr", "Nat"]
      let n := s!"o{k}"
      let det := if ← chance 40 then "det " else ""
      if ← chance 75 then results := results.push s!"{det}{n}: {ty}"
      else body := body ++ s!"    {det}exists {n}: {ty}\n"
      let guard ← if ← chance 30 then pure s!"when x > {← below 4}, " else pure ""
      let isRec := ty == "Sbox" || ty == "Sr"
      let e ← if isRec then do
          if ← chance 70 then pure s!"{n}.v = {← int} and {n}.w = {← int}" else pure s!"{n}.w > {← int}"
        else do
          match ← below 3 with
          | 0 => pure s!"{n} = {← int}"
          | 1 => pure s!"{n} > {← int}"
          | _ => pure s!"{n} != {← int}"
      body := body ++ s!"    ensure e{k}: {guard}{e}\n"
      if ← chance 30 then
        let v := if isRec then s!"{n}.v" else n
        let b ← below 3
        body := body ++ s!"    expect x{k}: {v} >= {b}\n"
    let rs := if results.isEmpty then "" else s!": ({", ".intercalate results.toList})"
    out := out ++ s!"\npub proc so{c}(x: Int, y: Int){rs} \{\n{body}}\n"
  return out

end FrenTest.FuzzFrontends.Wide
