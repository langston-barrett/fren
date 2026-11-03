-- keep-sorted start
import FrenCli.Search
import Lean.CoreM
-- keep-sorted end

/-! `smallValuesMemo` against its formulation before runtime round 12, on
generated data types: the old one made, of each variant, up to `cap`
combinations of its fields' values and kept `smallInterleaved cap` of
them all; the new one makes only those that `smallInterleaved` reads
(`combosSize`, `interleavedCounts`, `roundRobin`). The two must give the
same values, in the same order, since they decide which inputs testing
draws. This checks the three parts together, through `smallValues`
itself, on random multi-variant, multi-field, recursive and generic data
types, at several caps and depths. It is a test, over these generated
types, not a proof. -/

namespace Fren.Test.SmallValues

open FrenCli.Eval

/-- `smallValuesMemo` as it was before runtime round 12: the reference. -/
partial def oldMemo (sp : Spec) (w : World) (ints : Array Int) (strs : Array String) (cap : Nat)
    (depth : Nat) (ty : VTy) : StateM (Std.HashMap (Nat × VTy) (Array Val)) (Array Val) := do
  if let some vs := (← get)[(depth, ty)]? then return vs
  let go := oldMemo sp w ints strs cap
  let vs ← match ty with
    | .bool => pure #[.bool false, .bool true]
    | .int => pure (ints.map .int)
    | .nat => pure ((ints.filter (0 ≤ ·)).map .int)
    | .string => pure ((strs ++ #["", "a", "b"].filter (!strs.contains ·)).map .str)
    | .set t => pure (smallSets (← go depth t))
    | .seq t => pure (smallSeqs (← go depth t))
    | .rel a b => do
      let as := (← go depth a).extract 0 3
      let bs := (← go depth b).extract 0 3
      let pairs := as.flatMap fun x => bs.map (Val.pair x ·)
      let mut out := #[.set #[]] ++ (pairs.extract 0 6).map (Val.setOf #[·])
      if a == b && as.size ≥ 3 then
        out := out.push (Val.setOf #[.pair as[0]! as[1]!, .pair as[1]! as[2]!])
      pure out
    | .abstract s => pure ((Array.range (w.size s)).map (.abs s))
    | .newtype _ u => go depth u
    | .param _ => pure #[]
    | .data p targs =>
      match sp.data.find? p with
      | none => pure #[]
      | some d => do
        let mut each : Array (Array Val) := #[]
        for c in d.ctors, idx in [0:d.ctors.size] do
          if depth == 0 && !c.fields.isEmpty then continue
          let mut combos : Array (Array Val) := #[#[]]
          for (_, t) in c.fields do
            combos := extendCombos cap combos (← go (depth - 1) (t.subst targs))
          each := each.push (combos.map (.ctor p idx ·))
        pure (smallInterleaved cap each)
  modify (·.insert (depth, ty) vs)
  return vs

/-- A random number below `n`, from a linear congruential generator. -/
def next (n : Nat) : StateM Nat Nat := do
  let s := ((← get) * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  set s
  return (s / 2 ^ 33) % n

/-- The name of the `j`th generated data type. -/
def dName (j : Nat) : Lean.Name := .mkSimple s!"D{j}"

/-- A random field type, among `n` data types: a scalar, another data type
or this one (generic, with `Bool` as its argument, or not), a type
parameter, or a set, sequence or relation of a scalar or a data type. -/
partial def genTy (n : Nat) (d : Nat) : StateM Nat VTy := do
  match ← next (if d == 0 then 6 else 10) with
  | 0 => return .bool
  | 1 => return .int
  | 2 => return .nat
  | 3 => return .string
  | 4 => return .param 0
  | 5 => return .data (dName (← next n)) []
  | 6 => return .data (dName (← next n)) [← genTy n (d - 1)]
  | 7 => return .set (← genTy n (d - 1))
  | 8 => return .seq (← genTy n (d - 1))
  | _ => return .rel (← genTy n (d - 1)) (← genTy n (d - 1))

/-- A random spec of up to four data types, each of up to 30 variants of
up to three fields. -/
def genSpec : StateM Nat (Spec × Nat) := do
  let n := (← next 4) + 1
  let mut data : Lean.NameMap DataDef := {}
  for j in [0:n] do
    let wide := (← next 3) == 0
    let nCtors := (← next (if wide then 30 else 6)) + 1
    let mut ctors := #[]
    for k in [0:nCtors] do
      let nFields ← next 4
      let mut fields := #[]
      for _ in [0:nFields] do fields := fields.push (.anonymous, ← genTy n 1)
      ctors := ctors.push { name := .mkSimple s!"C{k}", fields }
    data := data.insert (dName j) { path := dName j, isRecord := false, ctors }
  return ({ data }, n)

/-- Where the old and the new `smallValues` differ on `specs` generated
specs (300 in `lake test`'s `smallValues` job), for each of their data
types, generic or not, at caps 0, 1, 2, 5, 9 and 24 and depths 0 to 3,
and, at 300 specs, too few that `cap` cut, which `roundRobin` alone
decides. -/
def differences (specs : Nat) : Array String := Id.run do
  let mut failures := #[]
  let mut seed := 17
  let mut cut := 0
  for _ in [0:specs] do
    let ((sp, n), s) := genSpec.run seed
    seed := s
    let w : World := { seed := 0 }
    for j in [0:n] do
      for ty in [VTy.data (dName j) [], .data (dName j) [.bool]] do
        for cap in [0, 1, 2, 5, 9, 24] do
          for depth in [0:4] do
            let new := smallValues sp w #[0, 1, -2] #["x"] cap depth ty
            let old := (oldMemo sp w #[0, 1, -2] #["x"] cap depth ty).run' {}
            if 0 < cap && new.size == cap then cut := cut + 1
            if new != old then
              failures := failures.push (s!"`smallValues` differs from its old formulation on {repr ty} " ++
                s!"at cap {cap}, depth {depth}: {new.size} values, not {old.size}")
  if specs ≥ 300 && cut < 1000 then failures := failures.push s!"only {cut} cases were cut to `cap`"
  return failures

-- A few specs at build time, that it runs at all; the job checks 300,
-- compiled, rather than in the interpreter in every `lake build`, where
-- they took some 25 s on a Mac and 30 to 80 s on CI.
#guard differences 3 == #[]

end Fren.Test.SmallValues
