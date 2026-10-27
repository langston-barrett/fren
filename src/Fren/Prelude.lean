-- keep-sorted start
import Fren.Elab
import FrenCore.Prelude
-- keep-sorted end

/-!
# The prelude (`Reqs/Lang/Prelude`)

Fren's prelude, `FrenCore/Prelude.fren`, elaborated into its own module
(`Core.preludeModule`), so that every file that imports `Fren.Spec` has its
items, as every input of the `fren` command has. Its types are Lean's own
(`Core.leanTypes`): `Option<T>` is `Option T`, and `Result<T, E>` is
`Except E T`, for which nothing is generated but what Fren needs of every
enumeration and Lean does not declare: a selector for each value of each
payload, and `Except`'s decidable equality.
-/

open Lean Elab Command

namespace Fren.Prelude

/-! The selectors of the payloads of the prelude's types' Lean
constructors, under `Fren.preludeSelectors`, as `Fren.selectorName` names a
generated constructor's, with the type's parameters implicit and an
`Inhabited` instance of each, for `default`. lean-smt gives the solver
their fields' selectors (`Fren.leanSmtField`). -/

def Option.some.x0 {α : Type} [Inhabited α] (v : _root_.Option α) : α :=
  match v with
  | .some x => x
  | .none => default

def Except.ok.x0 {ε α : Type} [Inhabited ε] [Inhabited α] (v : _root_.Except ε α) : α :=
  match v with
  | .ok x => x
  | .error _ => default

def Except.error.x0 {ε α : Type} [Inhabited ε] [Inhabited α] (v : _root_.Except ε α) : ε :=
  match v with
  | .error x => x
  | .ok _ => default

/-- `Except`'s values are equal if they are built alike, as every Fren
enumeration's are (`Reqs/Lang/Types`); Lean has no instance of its own. -/
instance decEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (_root_.Except ε α) := fun a b =>
  match a, b with
  | .ok x, .ok y => if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .error x, .error y => if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .ok _, .error _ => isFalse (by intro e; cases e)
  | .error _, .ok _ => isFalse (by intro e; cases e)

end Fren.Prelude

namespace Fren

/-- Elaborates the prelude's text into its module, with its messages, of
which it has none. -/
def elabPrelude : CommandElabM Unit := do
  let inputCtx := Parser.mkInputContext Core.preludeSource "FrenCore/Prelude.fren"
  let outer ← getLocal
  modifyLocal fun l => { l with currentModule := Core.preludeModule }
  let s ← get
  let st ← IO.processCommands inputCtx {} { s with messages := {} }
  set { st.commandState with messages := st.commandState.messages.toList.foldl (·.add) s.messages, infoState := s.infoState }
  modifyLocal fun l => { l with currentModule := outer.currentModule }

end Fren

open Fren.Lang

run_cmd Fren.elabPrelude
