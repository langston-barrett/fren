-- keep-sorted start
import Fren.View
-- keep-sorted end

open Fren.Lang

mod recursive_dependency

-- A modular caller may use a contract whose own proof is inconclusive.
-- fren-covers: lang::recursive_facts
pub enum T { Z, S(T) }

pub fn weak(t: T): (r: Int) {
    out r := match t {
        T::Z => 0,
        T::S(a) => 1 + weak(a),
    }
    ensure not_minus_one: r != -1
}

pub fn copy(t: T): (r: Int) {
    out r := match t {
        T::Z => 0,
        T::S(a) => if copy(a) != -1 then weak(a) else 0,
    }
    ensure not_minus_one: r != -1
}

-- Conditional dependency theorems must propagate the same modular rule.
pub fn copy_again(t: T): (r: Int) {
    out r := match t {
        T::Z => 0,
        T::S(a) => if copy_again(a) != -1 then copy(a) else 0,
    }
    ensure not_minus_one: r != -1
}

#guard_msgs (drop warning, drop info) in
#fren_check

open recursive_dependency

-- These must exist, and their assumptions must be explicit in Lean.
example (h : ∀ t, weak t ≠ -1) (t : T) : copy t ≠ -1 := by
  exact Fren.Generated.recursive_dependency.copy.not_minus_one.holds h t

example (h : ∀ t, weak t ≠ -1) (hcopy : ∀ t, copy t ≠ -1)
    (t : T) : copy_again t ≠ -1 := by
  exact Fren.Generated.recursive_dependency.copy_again.not_minus_one.holds h hcopy t
