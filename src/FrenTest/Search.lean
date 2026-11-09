-- keep-sorted start
import FrenCli.Quick
-- keep-sorted end

/-!
The defined outputs that the inputs alone give (`Comp.earlyDefs`), found
whatever order they are declared in (`Reqs/Lang/Procedures#members`).
-/

open FrenCli.Eval

-- `a := b + 1` comes before `b := x`, which it mentions; `c` mentions an
-- output that is not defined, so the inputs alone do not give it.
#guard
  let v (n : Lean.Name) (role : Fren.Core.Role) : Var := { name := n, ty := .int, role, isPub := true }
  let c : Comp := { path := `c, vars := #[v `x .input, v `a .output, v `b .output, v `c .output, v `y .output],
                    constraints := #[], insts := #[]
                    defs := #[(`a, .bin .add (.var `b) (.lit (.int 1))), (`b, .var `x), (`c, .var `y)] }
  c.earlyDefs == #[`b, `a]

/- A procedure's random inputs and the interpretation of its own sort stay
   the same when an unrelated abstract type is added to the reference. -/
section SeedIsolation

open Lean

def seedIsolationSamples (sp : Spec) : Array (Nat × Option Val × Option Val) := Id.run do
  let c : Comp := { path := `example.p, vars := #[
    { name := `x, role := .input, ty := .abstract `S, isPub := true },
    { name := `y, role := .input, ty := .int, isPub := true }], constraints := #[], insts := #[] }
  let pre := sp.admitAtoms c (fun _ => none)
  let mut rng : Rng := ⟨mix 0 (hash c.path)⟩
  let mut samples := #[]
  for _ in [0:100] do
    let (w, next) := (World.random sp).run rng
    let (admitted, next) := (sp.admit w c #[-1, 0, 1, 2] #[] none pre).run next
    rng := next
    samples := samples.push (w.size `S, admitted.bind (·.env[`x]?), admitted.bind (·.env[`y]?))
  return samples

#guard
  let a := seedIsolationSamples { sorts := #[`S] }
  let b := seedIsolationSamples { sorts := #[`Unrelated, `S] }
  a == b && a.any (fun (_, x, y) => x.isSome && y.isSome)

end SeedIsolation
