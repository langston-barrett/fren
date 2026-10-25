-- keep-sorted start
import FrenCli.Search
-- keep-sorted end

/-!
The defined outputs that the inputs alone give (`Comp.earlyDefs`), found
whatever order they are declared in (`Reqs/Lang/Components#members`).
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
