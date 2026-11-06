-- keep-sorted start
import FrenTest.FuzzFrontends.Random
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends.Wide

/-! ### Guards of quantifiers -/

/-- The declarations that `guardsProc` quantifies over: newtypes over
`Int` and `Nat`, a newtype over a newtype, one that is not ordered, an
ordered record and an ordered enumeration. -/
def guardDecls : String :=
  "pub ordered struct Gm(Int)\npub ordered struct Gn(Nat)\npub ordered struct Go(Gm)\npub struct Gp(Int)\n" ++
  "pub ordered struct Gr { x: Int, y: Int }\npub ordered enum Ge { A, B, C }\n" ++
  "pub type Gb = b: Int where invariant: b is 0..=3\n"

/-- An operand of a guard: how it reads the bound name `x`, and a constant
of its type, which a bound or a member may be. -/
structure GuardForm where
  text : String
  lit : R String
  /-- A collection of the operand's type, for a membership. -/
  coll : R String
  /-- Whether `k`, an `Int`, may bound it. -/
  int : Bool := false

instance : Inhabited GuardForm := ⟨{ text := "x", lit := pure "0", coll := pure "s" }⟩

def intLit : R String := do
  let n ← below 6
  return if (← chance 15) then s!"-{n}" else toString n

/-- The ways a guard may read a bound name of the type `ty`, by its fields
and orderings, each with constants of its type. -/
def guardForms (ty : String) (x : String) : Array GuardForm :=
  let ints : R String := intLit
  let natLit : R String := do return toString (← below 6)
  let intColl (lit : R String) : R String := do
    match ← below 3 with
    | 0 => return "s"
    | 1 => return "q"
    | _ => return s!"\{{← lit}, {← lit}}"
  let wrapColl (lit : R String) : R String := do
    if ← chance 50 then return s!"\{{← lit}, {← lit}}" else return s!"[{← lit}, {← lit}]"
  let int (t : String) (lit : R String) : GuardForm := { text := t, lit, coll := intColl lit, int := true }
  match ty with
  | "Int" | "Gb" => #[int x ints]
  | "Nat" => #[int x natLit]
  | "Gm" =>
    let gm : R String := do return s!"Gm({← intLit})"
    #[{ text := x, lit := gm, coll := wrapColl gm }, int s!"{x}.0" ints]
  | "Gn" =>
    let gn : R String := do return s!"Gn({← natLit})"
    #[{ text := x, lit := gn, coll := wrapColl gn }, int s!"{x}.0" natLit]
  | "Go" =>
    let gm : R String := do return s!"Gm({← intLit})"
    let go : R String := do return s!"Go(Gm({← intLit}))"
    #[{ text := x, lit := go, coll := wrapColl go }, { text := s!"{x}.0", lit := gm, coll := wrapColl gm },
      int s!"{x}.0.0" ints, int s!"({x}).0.0" ints]
  | "Gp" => #[int s!"{x}.0" ints, int s!"({x}).0" ints]
  | "Gr" =>
    let gr : R String := do return s!"Gr \{ x := {← intLit}, y := {← intLit} }"
    #[{ text := x, lit := gr, coll := wrapColl gr }, int s!"{x}.x" ints]
  | "Ge" =>
    let ge : R String := do return s!"Ge::{← pick #["A", "B", "C"]}"
    #[{ text := x, lit := ge, coll := wrapColl ge }]
  | _ =>
    let str : R String := do pick #["\"\"", "\"a\"", "\"ab\"", "\"b\""]
    #[{ text := x, lit := str, coll := wrapColl str }]

/-- A conjunct of a guard of the bound name `x` of the type `ty`: a
comparison of one of its forms, on either side, with each operator, a
chain of two, a membership, or a conjunct about something else. -/
def guardConjunct (ty x : String) : R String := do
  let f ← pick (guardForms ty x)
  let bound : R String := do
    if f.int && (← chance 30) then pick #["k", "k + 1", "q.len"] else f.lit
  match ← below 6 with
  | 0 | 1 =>
    let op ← pick #["<", "<=", ">", ">="]
    if ← chance 50 then return s!"{f.text} {op} {← bound}" else return s!"{← bound} {op} {f.text}"
  | 2 => return s!"{← bound} {← pick #["<", "<="]} {f.text} {← pick #["<", "<="]} {← bound}"
  | 3 | 4 => return s!"{f.text} in {← f.coll}"
  | _ => pick #["k > 0", "true"]

/-- A procedure of guarded quantifiers alone, always enumerated, over
each type that a guard may bound or not (`lang::range_domain`), its
operands read through fields (`lang::name_alone`), with ranges with one
or both bounds, memberships in sets and sequences, and each comparison
operator. -/
def guardsProc (name : String) : R String := do
  let tys := #["Int", "Nat", "Gb", "Gm", "Gn", "Go", "Gp", "Gr", "Ge", "String"]
  let mut body := ""
  let n := (← below 3) + 1
  for j in [0:n] do
    let ty ← pick tys
    let x := "x"
    let guard := " and ".intercalate (← (List.range ((← below 3) + 1)).mapM fun _ => guardConjunct ty x)
    let f ← pick (guardForms ty x)
    let inst := s!"{f.text} != {← f.lit}"
    let q ← if ← chance 60 then pure s!"forall ({x}: {ty}), when {guard}, {inst}"
      else pure s!"exists ({x}: {ty}), {guard} and {inst}"
    body := body ++ s!"    ensure r{j}: b{j}? iff ({q})\n    expect e{j}: b{j}?\n"
  let outs := ", ".intercalate ((List.range n).map (s!"b{·}?"))
  let size := if ← chance 10 then 3 else 2
  return s!"\nset_option fren.lint.undecidable \"allow\" in\nset_option fren.lint.chainable_comparison \"allow\" in\n" ++
    s!"set_option fren.enumeration.size {size} in\nset_option fren.evidence \"enumerated\" in\n" ++
    s!"pub proc {name}(k: Int, s: Set<Int>, q: Seq<Int>): ({outs}) \{\n{body}}\n"

/-- A spec of guarded quantifiers alone (`--guards`). -/
def genGuards : R String := do
  let mut out := "mod fz\n\n" ++ guardDecls
  for i in [0:(← below 3) + 2] do
    out := out ++ (← guardsProc s!"g{i}")
  return out

end FrenTest.FuzzFrontends.Wide
