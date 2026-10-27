-- keep-sorted start
import Fren.View
-- keep-sorted end
open Fren.Lang

-- A generic function's generated definition (`Reqs/Generated#generic-functions`):
-- an explicit `Type` parameter for each type parameter, with its
-- `Inhabited` instance, and the solver sees its body at each application's
-- instance.
mod generic_functions

pub enum Opt<T> { None, Some(T) }

fn unwrap_or<T>(o: Opt<T>, d: T): T := match o { Opt::Some(x) => x, Opt::None => d }

comp c {
  in x: Opt<Int>
  pub det out y: Int := unwrap_or(x, 0)

  expect missing: when x = Opt::None, y = 0
}

/--
info: @[reducible] def Fren.Generated.generic_functions.unwrap_or : (T : Type) →
  [#inhabited : Inhabited T] → generic_functions.Opt T → T → T :=
fun T [Inhabited T] o d =>
  if o = generic_functions.Opt.Some (generic_functions.Opt.Some.x0 o) then generic_functions.Opt.Some.x0 o else d
-/
#guard_msgs in
#print generic_functions.unwrap_or

-- An ordinary Lean definition, applied at an instance.
example : generic_functions.unwrap_or Int (.Some 3) 0 = 3 := by simp [generic_functions.unwrap_or, generic_functions.Opt.Some.x0]

/-- info: fren: 4 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
#fren_check
