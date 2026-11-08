module

namespace FrenBase

/-- A path component distinguishes written names from generated items. The kind
is deliberately open: passes may introduce kinds without a global registry. -/
public inductive ItemComponent where
  | named (name : String)
  | generated (kind : String) (index : Nat)
  deriving Repr, DecidableEq, BEq

/-- A structural item path. `root` is the empty enclosing path, not an item. -/
public inductive ItemId where
  | root
  | child (parent : ItemId) (component : ItemComponent)
  deriving Repr, DecidableEq, BEq

namespace ItemId

@[expose] public def named (parent : ItemId) (name : String) : ItemId :=
  .child parent (.named name)

@[expose] public def generated (parent : ItemId) (kind : String) (index : Nat) : ItemId :=
  .child parent (.generated kind index)

@[expose] public def parent : ItemId → Option ItemId
  | .root => none
  | .child p _ => some p

@[expose] public def component : ItemId → Option ItemComponent
  | .root => none
  | .child _ c => some c

/-- Components in enclosing-to-enclosed order. -/
@[expose] public def components : ItemId → List ItemComponent
  | .root => []
  | .child p c => p.components ++ [c]

/-- Readable display only: names and kinds are not escaped, so this is not a
serialization and distinct paths may render alike. Root renders as the empty string. -/
@[expose] public def render (id : ItemId) : String :=
  let parts := id.components.map fun c => match c with
    | .named n => n
    | .generated k i => "{" ++ k ++ "#" ++ toString i ++ "}"
  String.intercalate "." parts

@[simp] public theorem parent_child (p : ItemId) (c : ItemComponent) :
    (child p c).parent = some p := rfl
@[simp] public theorem component_child (p : ItemId) (c : ItemComponent) :
    (child p c).component = some c := rfl
@[simp] public theorem child_eq_child (p q : ItemId) (c d : ItemComponent) :
    child p c = child q d ↔ p = q ∧ c = d := by
  simp only [ItemId.child.injEq]

/-- A non-root path is recovered from its observed parent and component. -/
public theorem rebuild (id p : ItemId) (c : ItemComponent)
    (hp : id.parent = some p) (hc : id.component = some c) : id = child p c := by
  cases id with
  | root => simp [parent] at hp
  | child parent component =>
    change some parent = some p at hp
    change some component = some c at hc
    simp only [Option.some.injEq] at hp hc
    cases hp
    cases hc
    rfl

public theorem named_ne_generated (p q : ItemId) (name kind : String) (index : Nat) :
    named p name ≠ generated q kind index := by
  simp [named, generated]

end ItemId
end FrenBase
