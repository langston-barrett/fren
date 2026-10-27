-- keep-sorted start
import Impls.Check
import Impls.Scope
import Reqs.Modules
-- keep-sorted end
open Fren.Lang

/-! # Name resolution and visibility (`Reqs/Modules`) -/

namespace Fren.Impls

open Fren.Core (Binding Resolution resolution lookup lookupResolution firstSegment itemHidesPrelude itemShadowingAccepted shadowingAccepted visibleFrom
  Parent memberAccepted)

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
  | .prelude => .Prelude
  | .unbound => .Unbound

-- Over `Nat`, so `decide` does not apply: a proof by cases.
impl resolve_layers: modules::resolve_layers for (l : Bool) (k : Nat) (p : Bool) {
  local? := l,
  n_glob := k,
  prelude? := p,
  result := toResolution (resolution l k p),
} by
  intro l k p _
  cases l <;> cases p <;> rcases k with _ | _ | k <;> simp [fren_spec, resolution, toResolution] <;> omega

/-- A context without the prelude, as `Table.resolvePath` reads it. -/
def withoutPrelude (cx : Fren.Core.Context String) : Fren.Core.Context String := { cx with prelude := [] }

-- For every context and every first segment: what it resolves to among the
-- items and imports that `Context.bindings` lists, with and without the
-- prelude, by `lookup`, read as `lookupResolution`, all of which
-- `Table.resolvePath` calls.
impl resolve: modules::resolve for (cx : Fren.Core.Context String) (n : String) {
  bindings := Fren.FinSet.ofList (cx.itemScope.bindings.map toBinding),
  nearer := Fren.FinSet.ofList ((withoutPrelude cx).itemScope.bindings.map toBinding),
  name := n,
  lookup := toLookup (lookup cx.itemScope.bindings n),
  result := toResolution (lookupResolution (lookup cx.itemScope.bindings n) (lookup (withoutPrelude cx).itemScope.bindings n)),
} by
  intro cx n _
  obtain ⟨hd, he⟩ := scope cx.itemScope.bindings n (fun _ _ => Nat.zero_le _)
  obtain ⟨hd', he'⟩ := scope (withoutPrelude cx).itemScope.bindings n (fun _ _ => Nat.zero_le _)
  refine ⟨_, _, _, _, _, _, _, _, ⟨rfl, ?_⟩, trivial, ⟨⟨rfl, rfl⟩, hd, fun _ _ => Nat.zero_le _, he⟩,
    ⟨⟨rfl, rfl⟩, hd', fun _ _ => Nat.zero_le _, he'⟩⟩
  simp only [modules.resolve.def.result]
  cases h : lookup cx.itemScope.bindings n with
  | found b =>
    cases h' : lookup (withoutPrelude cx).itemScope.bindings n <;>
      cases b with | mk _ k _ _ => cases k <;>
        simp [toLookup, toBindingKind, lookupResolution, toResolution, lang.Lookup.Found.x0]
  | _ => simp [toLookup, lookupResolution, toResolution, lang.Lookup.Found.x0]

interp modules::Path := Lean.Name

-- The length of a sequence of two paths or more, as the spec compares it.
theorem two_ne_one (n : Nat) : ¬((n : Int) + 1 + 1 = 1) := by omega
theorem one_lt_two_more (n : Nat) : 1 < (n : Int) + 1 + 1 := by omega

-- For every scope's layers, with the function that resolution uses
-- (`Fren.Core.Table.resolvePath`).
impl first_segment: modules::first_segment for (d o p : List Lean.Name) {
  declared := Fren.Seq.ofList d,
  opened := Fren.Seq.ofList o,
  prelude := Fren.Seq.ofList p,
  result := toResolution (firstSegment d.toArray o.toArray p.toArray).1,
  target := Fren.Seq.ofList (firstSegment d.toArray o.toArray p.toArray).2.toList,
} by
  intro d o p _
  rcases d with _ | ⟨a, d⟩ <;> rcases o with _ | ⟨b, _ | ⟨c, o⟩⟩ <;> rcases p with _ | ⟨e, p⟩ <;>
    simp [fren_spec, firstSegment, resolution, toResolution, Fren.Seq.ext_iff, Fren.Seq.«at», Fren.Seq.slice,
      two_ne_one, one_lt_two_more]

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

-- For every fresh item's layers, with the function that both front ends'
-- checks of an item's name use (`Fren.Core.Table.checkItemShadowing`).
impl item_shadowing: modules::item_shadowing for (o p : List Lean.Name) (b : Bool) {
  opened := Fren.Seq.ofList o,
  prelude := Fren.Seq.ofList p,
  bang? := b,
  hides? := itemHidesPrelude o.toArray p.toArray,
  accepted? := itemShadowingAccepted o.toArray p.toArray b,
} by
  intro o p b _
  rcases o with _ | ⟨x, _ | ⟨y, o⟩⟩ <;> rcases p with _ | ⟨e, p⟩ <;> cases b <;>
    simp [fren_spec, itemShadowingAccepted, itemHidesPrelude, firstSegment, resolution, shadowingAccepted] <;> rfl

end Fren.Impls
