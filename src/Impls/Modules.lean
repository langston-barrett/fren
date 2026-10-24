-- keep-sorted start
import Impls.Check
-- keep-sorted end
open Fren.Lang

/-! # Name resolution and visibility (`Reqs/Modules`) -/

namespace Fren.Impls

open Fren.Core (Resolution resolution visibleFrom Parent memberAccepted)

-- A module is its path, and a descendant of each proper prefix of it.
interp modules::ModuleName := Lean.Name
interp modules::descends? := fun m a => a.isPrefixOf m && m != a

theorem isPrefixOf_self (n : Lean.Name) : n.isPrefixOf n = true := by
  cases n <;> simp [Lean.Name.isPrefixOf]

-- For every item and every module, with `visibleFrom`, which resolution uses.
impl item_visible: modules::item_visible for (here middle : Lean.Name) (i : Fren.Core.Item) {
  is_pub? := i.isPub,
  owner := i.owner,
  here := here,
  middle := middle,
  visible? := visibleFrom here i,
} by
  intro here middle i _
  by_cases h : here = i.owner <;> simp [fren_spec, visibleFrom, Fren.Core.isDescendant, isPrefixOf_self, h]

def toResolution : Resolution → modules.Resolution
  | .local => .Local
  | .glob => .Glob
  | .ambiguous => .Ambiguous
  | .unbound => .Unbound

-- Over `Nat`, so `decide` does not apply: a proof by cases.
impl resolve: modules::resolve for (l : Bool) (k : Nat) {
  local? := l,
  n_glob := k,
  result := toResolution (resolution l k),
} by
  intro l k _
  cases l <;> rcases k with _ | _ | k <;> simp [fren_spec, resolution, toResolution] <;> omega

instance : Fren.Finite Parent := ⟨[.module, .enum, .other], by intro x; cases x <;> simp⟩

def toKind : Parent → modules.Kind
  | .module => .Module
  | .enum => .Enum
  | .other => .Other

impl member: modules::member for (p : Parent) (found visible : Bool) {
  parent := toKind p,
  found? := found,
  visible? := visible,
  accepted? := memberAccepted p found visible,
}

end Fren.Impls
