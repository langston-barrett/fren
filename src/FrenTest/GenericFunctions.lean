-- keep-sorted start
import Fren.Impl
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

proc c(x: Opt<Int>): (det y: Int) {
  out y := unwrap_or(x, 0)

  expect missing: when x = Opt::None, y = 0
}

/--
info: @[reducible] def Fren.Generated.generic_functions.unwrap_or : (T : Type) →
  [#inhabited : Inhabited T] → generic_functions.Opt T → T → T :=
fun T [Inhabited T] o d =>
  match o with
  | generic_functions.Opt.Some x => x
  | generic_functions.Opt.None => d
-/
#guard_msgs in
#print generic_functions.unwrap_or

-- An ordinary Lean definition, applied at an instance.
example : generic_functions.unwrap_or Int (.Some 3) 0 = 3 := by simp [generic_functions.unwrap_or]

-- Compiled, so that compiled code runs it, and `decide` reduces it.
#guard generic_functions.unwrap_or Int .None 5 == 5
example : generic_functions.unwrap_or Int (.Some 3) 0 = 3 := by decide

/-- info: fren: 4 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
#fren_check

-- A generic function without a body (`Reqs/Generated#generic-functions`):
-- a constant that takes each type parameter, and its `Inhabited`
-- instance, first, which a component that applies it takes as a parameter,
-- at the instance, and an interpretation gives, with each instance a
-- function of its own (`Reqs/Impl#interpretations`).
mod generic_uninterpreted

fn choose<T>(a: T, b: T): T
    ensure either: choose(a, b) = a or choose(a, b) = b

proc at_int(x: Int): (det y: Int) {
  out y := choose(x, 0)

  expect either: y = x or y = 0
}

/--
info: generic_uninterpreted.at_int.ensures : ((T : Type) → [#inhabited : Inhabited T] → T → T → T) → Int → Int → Prop
-/
#guard_msgs in #check @generic_uninterpreted.at_int.ensures

-- Its interpretation proves the postcondition at every instance.
interp choose := fun _ _ a _ => a by
  intro _ _ a b
  simp [generic_uninterpreted.choose.either]

/-- info: fren: 8 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
#fren_check
