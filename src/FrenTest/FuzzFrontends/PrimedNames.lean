-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-- The bound names of a quantifier of `primedNames`, from position `k`:
one or two, each with its position and type, `zi` or `zj` at position 0
and the other at 1, as a list of binders and as written. -/
def primedBinders (tys : Array String) (first : String) (k : Nat) : R (Array (String × Nat × String)) := do
  let other := if first == "zi" then "zj" else "zi"
  let names := if k == 0 then #[first, other] else #[other]
  let n := if names.size == 2 && (← chance 50) then 2 else 1
  return (names.extract 0 n).mapIdx fun i x => (x, k + i, tys[k + i]!)

/-- A comparison of the bound name `x`, of type `t`, with a variable of
`primedNames` of a type it compares with, or another bound name of
`bound`, or a literal. -/
def primedAtom (tys : Array String) (bound : Array (String × Nat × String)) (x : String) (t : String) : R String := do
  let numeric (u : String) := u != "String"
  let fits (u : String) := if t == "String" then u == "String" else numeric u
  let vars := (#["zi", "zj"].flatMap fun n => #[0, 1].map fun k => (s!"{n}'{k}", tys[k]!)).filter (fits ·.2)
  let others := (bound.filter fun (y, _, u) => y != x && fits u).map (·.1)
  let rhs ← match ← below 4 with
    | 0 | 1 => pure (← pick vars).1
    | 2 => if others.isEmpty then pure (← pick vars).1 else pick others
    | _ => if t == "String" then pure "\"a\"" else do pure (toString (← below 3))
  let op ← if t == "String" then pick #["=", "!="] else pick #["=", "!=", "<", ">=", ">"]
  return s!"{x} {op} {rhs}"

/-- A quantifier of `primedNames` from position `k`, over bound names
whose symbols were those of its variables: one or two bound names, under
`forall` or `exists`, with or without a guard, and a quantifier within it
at the next position, now and then. -/
partial def primedQuant (tys : Array String) (first : String) (k : Nat) (outer : Array (String × Nat × String)) :
    R String := do
  let bs ← primedBinders tys first k
  let all ← chance 50
  let bound := outer ++ bs
  let binders := " ".intercalate (bs.toList.map fun (x, _, t) => s!"({x}: {t})")
  let atom : R String := do
    let (x, _, t) ← pick bound
    primedAtom tys bound x t
  let inner ← if bs.size == 1 && k == 0 && (← chance 40) then primedQuant tys first 1 bound else atom
  let body ← if ← chance 50 then pure s!"{← atom} {← pick #["and", "or"]} ({inner})" else pure inner
  let guard ← if all && (← chance 50) then pure s!"when {← atom}, " else pure ""
  return s!"{if all then "forall" else "exists"} {binders}, {guard}{body}"

/-- Variables named as the symbols of bound names and of second copies
were, `x'k` and `x'`, beside quantifiers whose bound names are `x` at
position `k`, of each type that is not listed, in expectations,
guarantees and a defined output, and a `det` output beside a variable
named as its copy was; and an enumerated procedure, whose variable `zm'`
was read as the copy of its `zm` (`cli::query_symbols`). -/
def primedNames : R String := do
  let tys ← #[0, 1].mapM fun _ => pick #["Int", "Nat", "String"]
  let first ← pick #["zi", "zj"]
  let params := ", ".intercalate ((#["zi", "zj"].flatMap fun n => #[0, 1].map fun k => s!"{n}'{k}: {tys[k]!}").toList)
  let mut body := ""
  for k in [0:(← below 3) + 1] do
    body := body ++ s!"    expect zpe{k}: {← primedQuant tys first 0 #[]}\n"
  if ← chance 50 then body := body ++ s!"    ensure zpq: {← primedQuant tys first 0 #[]}\n"
  let mut results := #[]
  if ← chance 50 then
    results := results.push "zd?"
    body := body ++ s!"    out zd? := {← primedQuant tys first 0 #[]}\n"
  if ← chance 60 then
    results := results ++ #["det zy: Int", "zy': Int"]
    let num := (#["zi'0", "zi'1", "zj'0", "zj'1"].zip (tys ++ tys)).filterMap fun (v, t) => if t != "String" then some v else none
    let e ← if num.isEmpty then do pure (toString (← below 3)) else pick num
    body := body ++ (← pick #[s!"    ensure zya: zy = zy' + {e}\n",
      s!"    ensure zya: zy' = {e}\n    ensure zyb: zy = zy'\n", s!"    ensure zya: zy = {e}\n"])
  let resultList := if results.isEmpty then "" else s!": ({", ".intercalate results.toList})"
  let mut out := s!"set_option fren.lint.undecidable \"allow\" in\npub proc zpn({params}){resultList} \{\n{body}}\n"
  if ← chance 50 then
    let rel ← pick #["zm' = Zpe::A", "zm' != Zpe::B", "zm = Zpf::C"]
    let exp ← pick #["when zo?, zm' = Zpe::A", "when zo?, zm' = Zpe::B", "zo? or zm = Zpf::D"]
    out := out ++ "\npub enum Zpe { A, B }\npub enum Zpf { C, D, F }\n\nset_option fren.evidence \"enumerated\" in\n" ++
      s!"pub proc zpk(zm': Zpe, zm: Zpf): (det zo?) \{\n    ensure r: zo? iff {rel}\n    expect e: {exp}\n}\n"
  return out

end FrenTest.FuzzFrontends.Wide
