module

public import Lean.Data.Name

namespace FrenBase

/-- A written name or a compiler-generated kind and position. -/
public inductive ItemComponent where
  | named (name : String)
  | generated (kind : String) (index : Nat)
  deriving Repr, DecidableEq, BEq

/-- An item path, backed by Lean's cached-hash names. The root is an empty
    enclosing path, not an item. -/
public structure ItemId where private mk ::
  private path : Lean.Name
  deriving Repr, DecidableEq, BEq, Hashable, ReflBEq, LawfulBEq

namespace ItemId

public def root : ItemId := ⟨.anonymous⟩

/-- Each generated component uses a numeric node after its kind; named
components use only a string node. The encoding is an implementation detail. -/
public def child (parent : ItemId) : ItemComponent → ItemId
  | .named name => ⟨.str parent.path name⟩
  | .generated kind index => ⟨.num (.str parent.path kind) index⟩

public def named (parent : ItemId) (name : String) : ItemId :=
  child parent (.named name)

public def generated (parent : ItemId) (kind : String) (index : Nat) : ItemId :=
  child parent (.generated kind index)

public def parent (id : ItemId) : Option ItemId :=
  match id.path with
  | .anonymous => none
  | .str p _ => some ⟨p⟩
  | .num (.str p _) _ => some ⟨p⟩
  | .num _ _ => none

public def component (id : ItemId) : Option ItemComponent :=
  match id.path with
  | .anonymous => none
  | .str _ name => some (.named name)
  | .num (.str _ kind) index => some (.generated kind index)
  | .num _ _ => none

private def collect : Lean.Name → List ItemComponent
  | .anonymous => []
  | .str p name => collect p ++ [.named name]
  | .num (.str p kind) index => collect p ++ [.generated kind index]
  | .num _ _ => []

/-- Components in enclosing-to-enclosed order. -/
public def components (id : ItemId) : List ItemComponent := collect id.path

/-- Readable display only: names and kinds are not escaped, so this is not a
serialization and distinct paths may render alike. Root renders as the empty string. -/
public def render (id : ItemId) : String :=
  let parts := id.components.map fun c => match c with
    | .named n => n
    | .generated k i => "{" ++ k ++ "#" ++ toString i ++ "}"
  String.intercalate "." parts

@[simp] public theorem parent_child (p : ItemId) (c : ItemComponent) :
    (child p c).parent = some p := by cases p; cases c <;> rfl
@[simp] public theorem component_child (p : ItemId) (c : ItemComponent) :
    (child p c).component = some c := by cases p; cases c <;> rfl
@[simp] public theorem child_eq_child (p q : ItemId) (c d : ItemComponent) :
    child p c = child q d ↔ p = q ∧ c = d := by
  cases p; cases q; cases c <;> cases d <;> simp [child, and_assoc]

public theorem rebuild (id p : ItemId) (c : ItemComponent)
    (hp : id.parent = some p) (hc : id.component = some c) : id = child p c := by
  cases id with
  | _ path =>
    cases path with
    | anonymous => simp [parent] at hp
    | str pre name =>
      simp [parent] at hp
      simp [component] at hc
      cases hp; cases hc; rfl
    | num pre index =>
      cases pre with
      | anonymous => simp [parent] at hp
      | num p i => simp [parent] at hp
      | str pre kind =>
        simp [parent] at hp
        simp [component] at hc
        cases hp; cases hc; rfl

public theorem named_ne_generated (p q : ItemId) (name kind : String) (index : Nat) :
    named p name ≠ generated q kind index := by
  simp [named, generated, child]

/-- Equal keys always have equal hashes; distinct keys may collide. -/
public theorem beq_eq_true_iff (a b : ItemId) : (a == b) = true ↔ a = b := by
  exact ⟨fun h => eq_of_beq h, fun h => h ▸ beq_self_eq_true _⟩

public theorem hash_eq_of_eq (a b : ItemId) (h : a = b) : hash a = hash b := by
  cases h; rfl

/-- The equality used by hash maps is compatible with the key hash. -/
public theorem hash_eq_of_beq (a b : ItemId) (h : (a == b) = true) : hash a = hash b :=
  hash_eq_of_eq a b (eq_of_beq h)

end ItemId
end FrenBase
