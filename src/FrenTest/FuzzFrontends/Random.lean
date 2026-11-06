-- keep-sorted start
import FrenCli.Search
-- keep-sorted end

open Lean FrenCli FrenCli.Eval

namespace FrenTest.FuzzFrontends

def pick (xs : Array α) [Inhabited α] : R α := do return xs[← below xs.size]!

def chance (pct : Nat) : R Bool := do return (← below 100) < pct

def rngOf (seed : Nat) : Rng := ⟨mix seed.toUInt64 0xf407⟩

end FrenTest.FuzzFrontends
