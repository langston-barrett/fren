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

-- Giving-site parts are numbered independently by the solver reader and
-- evaluator. Swapping their invariant labels must fail before pairing a
-- check with another part's expression, even when the names still match.
private def pairParts (labels : Array (Option String)) : Except Fren.Core.Msg Unit := do
  let parts : Array Constraint := labels.mapIdx fun k label =>
    { kind := .assume, name := .num `x k, e := .obligation low (.var `x), typed? := label }
  let callee : Comp := { path := `accept, vars := #[], constraints := #[], insts := #[], inputObligations := parts }
  let caller : Comp := {
    path := `caller, vars := #[], constraints := #[],
    insts := #[{ name := `c, comp := `accept, bindings := #[] }] }
  let core : Fren.Core.Comp String := {
    path := `caller, vars := #[], assumes := #[], reqs := #[], expects := #[], triggers := #[]
    insts := #[{
      name := `c, comp := `accept, bindings := "", behaviour := "",
      assumes := #[(.num `x 0, "low"), (.num `x 1, "high")],
      typed := #[(.num `x 0, "@invariant:low"), (.num `x 1, "@invariant:high")] }] }
  let _ ← FrenCli.pairCore { comps := #[callee] } caller core #[]
  pure ()

#guard (pairParts #[some "@invariant:low", some "@invariant:high"]).isOk

private def pairingError (labels : Array (Option String)) : String :=
  match pairParts labels with
  | .ok _ => ""
  | .error msg => msg.headline

#guard (pairingError #[some "@invariant:high", some "@invariant:low"]).startsWith "internal error:"
#guard (pairingError #[some "@invariant:low"]).contains "<missing>"
#guard (pairingError #[none, some "@invariant:high"]).contains "<missing>"

-- fren-covers: lang::subset_obligations
