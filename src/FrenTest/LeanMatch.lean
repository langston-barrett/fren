-- keep-sorted start
import Fren.Impl
import Fren.View
-- keep-sorted end
open Fren.Lang

/-! A defined function's Lean definition (`Reqs/Generated#matches`,
`Reqs/Generated#computable-definitions`): a Lean `match` where its patterns
are Lean's, compiled, and the solver's `if`s beside it. -/

mod lean_match

pub enum Opt<T> { None, Some(T) }

-- A function block, whose `let` becomes a `where` clause of its body.
pub fn first_or<T>(a: Opt<T>, b: Opt<T>, d: T): (r: T) {
    let fallback := match b { Opt::Some(y) => y, Opt::None => d }
    out r := match a { Opt::Some(x) => x, Opt::None => fallback }
}

-- A guard, which falls through to the arms after it.
pub fn clamp(o: Opt<Int>): Int := match o {
    Opt::Some(x) if x > 10 => 10,
    Opt::Some(x) => x,
    Opt::None => 0,
}

-- A literal within a pattern test: `if`s, as the solver's.
pub fn is_zero?(o: Opt<Int>) := o is Opt::Some(0)

/--
info: @[reducible] def Fren.Generated.lean_match.first_or : (T : Type) →
  [#inhabited : Inhabited T] → lean_match.Opt T → lean_match.Opt T → T → T :=
fun T [Inhabited T] a b d =>
  have «fallback@0» :=
    match b with
    | lean_match.Opt.Some y => y
    | lean_match.Opt.None => d;
  match a with
  | lean_match.Opt.Some x => x
  | lean_match.Opt.None => «fallback@0»
-/
#guard_msgs in
#print lean_match.first_or

#guard lean_match.first_or Int .None (.Some 2) 0 == 2
#guard lean_match.clamp (.Some 12) == 10 && lean_match.clamp (.Some 3) == 3 && lean_match.clamp .None == 0
#guard lean_match.«is_zero?» (.Some 0) && !lean_match.«is_zero?» .None

example (x : Int) : lean_match.first_or Int (.Some x) .None 0 = x := by simp [lean_match.first_or]
example : lean_match.clamp (.Some 12) = 10 := by decide

/-- info: fren: 3 passed, 0 failed, 0 inconclusive, 0 redundant -/
#guard_msgs in
#fren_check
