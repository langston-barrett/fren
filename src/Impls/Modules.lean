-- keep-sorted start
import Impls.Check
import Impls.Scope
import Reqs.Modules
-- keep-sorted end
open Fren.Lang

/-! # Name resolution and visibility (`Reqs/Modules`) -/

namespace Fren.Impls

open Fren.Core (Binding Resolution resolution visibleFrom Parent memberAccepted lookup)

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

-- For every scope of items and imports and every first segment: what it
-- resolves to, by `lookup`, read as `resolution`, both of which
-- `Table.resolvePath` calls.
impl resolve: modules::resolve for (l : List (Binding String String)) (n : String) {
  bindings := Fren.FinSet.ofList (l.map toBinding),
  name := n,
  lookup := toLookup (lookup l n),
  result := toResolution (resolution (lookup l n)),
} by
  intro l n _
  obtain ⟨hd, he⟩ := scope l n (fun _ _ => Nat.zero_le _)
  refine ⟨_, _, _, _, ⟨rfl, ?_⟩, trivial, ⟨⟨rfl, rfl⟩, hd, fun _ _ => Nat.zero_le _, he⟩⟩
  simp only [modules.resolve.def.result]
  cases h : lookup l n with
  | found b => cases b with | mk _ k _ _ => cases k <;> simp [toLookup, toBindingKind, resolution, toResolution, lang.Lookup.Found.x0]
  | _ => simp [toLookup, resolution, toResolution, lang.Lookup.Found.x0]

instance : Fren.Finite Parent := ⟨[.module, .enum, .other], by intro x; cases x <;> simp⟩

def toKind : Parent → modules.Kind
  | .module => .Module
  | .enum => .Enum
  | .other => .Other

-- For every segment after the first, and the members of what the one
-- before it resolved to, which `Table.walk` lists, by `resolves`.
impl member: modules::member for (p : Parent) (l : List (Binding String String)) (n : String) (visible : Bool) {
  parent := toKind p,
  members := Fren.FinSet.ofList (l.map toBinding),
  name := n,
  visible? := visible,
  found? := Fren.Core.resolves l n,
  accepted? := memberAccepted p (Fren.Core.resolves l n) visible,
} by
  intro p l n visible _
  obtain ⟨hd, he⟩ := scope l n (fun _ _ => Nat.zero_le _)
  refine ⟨_, _, _, _, ?_, ?_, ⟨⟨rfl, rfl⟩, hd, fun _ _ => Nat.zero_le _, he⟩⟩
  · simp only [modules.member.defs, modules.member.def.found?]
    unfold Fren.Core.resolves
    cases lookup l n <;> simp [toLookup, lang.Lookup.Found.x0]
  · simp only [modules.member.ensures, modules.member.ensure.rule]
    generalize Fren.Core.resolves l n = f
    cases p <;> cases f <;> cases visible <;> simp [toKind, memberAccepted]

end Fren.Impls
