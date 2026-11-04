-- keep-sorted start
import FrenCli.Enumerate
-- keep-sorted end

/-! Separate call-input invariants must keep their guards and their own
truth, including unknown values, rather than check whole-type membership. -/

open FrenCli.Eval
open Fren.Core (Cons Invariant)

private def nonnegative : Invariant := { name := `low, predicate := `low }
private def low : Cons := .predicate nonnegative
private def interpretation : Interp :=
  { defs := fun n => if n == `low then some (#[`n], .bin .ge (.bound `n) (.lit (.int 0)), .bool) else none }

private def value (c : Cons) (v : Val) : Option Val :=
  (Ex.obligation c (.lit v)).eval interpretation (fun _ => none)

#guard value low (.int (-1)) == some (.bool false)
#guard value low (.int 1) == some (.bool true)
#guard value (.fields `Pair [] #[(1, low)]) (.ctor `Pair 0 #[.int (-1), .int 1]) == some (.bool true)
#guard value (.payloads `Choice [] #[(1, 0, low)]) (.ctor `Choice 0 #[]) == some (.bool true)
#guard value (.payloads `Choice [] #[(1, 0, low)]) (.ctor `Choice 1 #[.int (-1)]) == some (.bool false)
#guard value (.newtype `Wrapped low) (.int (-1)) == some (.bool false)
#guard value (.elems false .int low) (Val.setOf #[.int 1, .int (-1)]) == some (.bool false)
#guard value (.elems true .int low) (.seq #[.int 1]) == some (.bool true)
#guard value (.pairs .int .int (some low) none) (Val.setOf #[.pair (.int 1) (.int (-1))]) == some (.bool true)
#guard value (.pairs .int .int none (some low)) (Val.setOf #[.pair (.int 1) (.int (-1))]) == some (.bool false)
#guard value (.pat .int (.int (some 0) (some 1))) (.int 2) == some (.bool false)
#guard value .atLeast0 (.int (-1)) == some (.bool false)

private def unknown : Cons := .predicate { nonnegative with predicate := `unknown }
#guard value (.fields `Pair [] #[(0, unknown)]) (.ctor `Pair 0 #[.int 1]) == none
#guard value (.elems true .int unknown) (.seq #[.int 1]) == none
#guard value (.all #[unknown, low]) (.int (-1)) == some (.bool false)
#guard value (.all #[unknown, low]) (.int 1) == none

-- Compilation must retain the invariant's dependence on the interpretation.
#guard ((Ex.obligation low (.lit (.int 1))).compile (fun _ => none) none).eval interpretation (fun _ => none) == some (.bool true)
-- Dependency discovery must include functions hidden inside an invariant.
#guard (Ex.obligation low (.var `x)).appsOf
  { defs := ({} : Lean.NameMap (Array Lean.Name × Ex × VTy)).insert `low
      (#[`n], .app `choose #[.bound `n], .bool) } == #[`choose]

-- fren-covers: lang::subset_obligations
