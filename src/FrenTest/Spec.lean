-- keep-sorted start
import Fren.Spec
-- keep-sorted end
open Fren.Lang

-- Specs can be written, and their generated definitions used, without the
-- checker or lean-smt.
mod light

pub enum Mode { On, Off }

pub comp switch {
  in mode: Mode
  pub out lit?
  req lit: lit? iff mode = Mode::On
}

example : light.switch.reqs .On true := by decide

-- `decide` quantifies over enums and `Bool`.
example : ∀ m lit?, light.switch.reqs m lit? ↔ (lit? = true ↔ m = .On) := by decide

/-- info: false -/
#guard_msgs in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  Lean.logInfo m!"{((← Lean.getEnv).getModuleIdx? `Smt).isSome}"
