-- keep-sorted start
import Fren.Impl
-- keep-sorted end
open Fren.Lang
mod impl_closed_obligations
pub type Atom
pub proc list_domain(items: Seq<Atom>): (count: Int) {
  assume nonempty: items != []
  ensure length: count = items.len
}
interp Atom := Lean.Name
open Lean Elab Command in
elab "#check_closed_obligation" : command => do
  let some comp := (← Fren.getState).comps.get? `impl_closed_obligations.list_domain
    | throwError "missing interpreted list component"
  let binder ← `(bracketedBinder| (xs : List Lean.Name))
  let items ← `(Fren.Lang.fren_impl_map| items := Fren.Seq.ofList xs)
  let count ← `(Fren.Lang.fren_impl_map| count := (xs.length : Int))
  let obligation ← liftTermElabM <| Fren.mkObligation comp #[binder.raw] #[items.raw, count.raw] true
  unless !obligation.stmt.hasMVar && !obligation.stmt.hasLevelMVar &&
      !obligation.never.hasMVar && !obligation.never.hasLevelMVar do
    throwError "an implementation statement escaped with unresolved metavariables"
#check_closed_obligation
