/-!
# Finite sets

`Fren.FinSet α`, the Lean type of Fren's `Set<T>` (`Reqs/Generated`): a list
up to having the same members. It needs no instance on `α` to exist, so an
abstract type's interpretation, which need only be inhabited, can be the
element type. Intersection, difference, `card` and decidable membership
need `DecidableEq α`, which the generated definitions get classically.

Each operation has a `simp` lemma that states its meaning by membership,
so that implementations over lists and arrays are proved by `simp`.
-/

namespace Fren

/-- Two lists with the same members. -/
def FinSet.Equiv (l₁ l₂ : List α) : Prop := ∀ x, x ∈ l₁ ↔ x ∈ l₂

instance FinSet.setoid (α : Type u) : Setoid (List α) where
  r := FinSet.Equiv
  iseqv := ⟨fun _ _ => Iff.rfl, fun h x => (h x).symm, fun h₁ h₂ x => (h₁ x).trans (h₂ x)⟩

/-- A finite set of values of `α`. -/
def FinSet (α : Type u) : Type u := Quotient (FinSet.setoid α)

namespace FinSet

variable {α : Type u}

/-- The set of the members of `l`. -/
def ofList (l : List α) : FinSet α := Quotient.mk _ l

def ofArray (a : Array α) : FinSet α := ofList a.toList

/-- Whether `x` is a member. -/
protected def Mem (s : FinSet α) (x : α) : Prop :=
  Quotient.liftOn s (fun l => x ∈ l) fun _ _ h => propext (h x)

instance : Membership α (FinSet α) := ⟨FinSet.Mem⟩

@[simp] theorem mem_ofList {x : α} {l : List α} : x ∈ ofList l ↔ x ∈ l := Iff.rfl

@[simp] theorem mem_ofArray {x : α} {a : Array α} : x ∈ ofArray a ↔ x ∈ a := by
  simp [ofArray]

theorem ind {p : FinSet α → Prop} (h : ∀ l, p (ofList l)) (s : FinSet α) : p s :=
  Quotient.inductionOn s h

/-- Two sets with the same members are equal. -/
theorem ext {s t : FinSet α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  induction s using ind; induction t using ind
  exact Quotient.sound h

theorem ext_iff {s t : FinSet α} : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t := ⟨fun h _ => h ▸ Iff.rfl, ext⟩

/-- `l` with each member once. -/
def nub [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => if a ∈ nub l then nub l else a :: nub l

theorem mem_nub [DecidableEq α] {x : α} : ∀ {l : List α}, x ∈ nub l ↔ x ∈ l
  | [] => by simp [nub]
  | a :: l => by
    have ih : x ∈ nub l ↔ x ∈ l := mem_nub
    unfold nub
    by_cases h : a ∈ nub l
    · have ha : a ∈ l := mem_nub.mp h
      simp only [h, if_true, ih, List.mem_cons]
      exact ⟨Or.inr, fun e => e.elim (fun e => e ▸ ha) id⟩
    · simp [h, ih]

theorem nodup_nub [DecidableEq α] : ∀ (l : List α), (nub l).Nodup
  | [] => by simp [nub]
  | a :: l => by
    unfold nub
    split
    · exact nodup_nub l
    · exact List.nodup_cons.mpr ⟨by assumption, nodup_nub l⟩

/-- A list without repeats is no longer than a list with all its members. -/
theorem length_le_of_nodup [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => by simp
  | a :: l₁, l₂, hn, hs => by
    have ⟨ha, hn'⟩ := List.nodup_cons.mp hn
    have hal : a ∈ l₂ := hs a (by simp)
    have := length_le_of_nodup (l₂ := l₂.erase a) hn' fun x hx =>
      (List.mem_erase_of_ne (show x ≠ a from fun e => ha (by rw [← e]; exact hx))).mpr (hs x (by simp [hx]))
    rw [List.length_erase_of_mem hal] at this
    have : 0 < l₂.length := List.length_pos_of_mem hal
    simp only [List.length_cons]; omega

/-- The number of members. -/
def card [DecidableEq α] (s : FinSet α) : Int :=
  Quotient.liftOn s (fun l => ((nub l).length : Int)) fun l₁ l₂ h => by
    have h₁ := length_le_of_nodup (nodup_nub l₁) fun x hx => mem_nub.mpr ((h x).mp (mem_nub.mp hx))
    have h₂ := length_le_of_nodup (nodup_nub l₂) fun x hx => mem_nub.mpr ((h x).mpr (mem_nub.mp hx))
    omega

@[simp] theorem card_ofList [DecidableEq α] (l : List α) : card (ofList l) = (nub l).length := rfl

instance : EmptyCollection (FinSet α) := ⟨ofList []⟩
instance : Inhabited (FinSet α) := ⟨∅⟩
instance : Singleton α (FinSet α) := ⟨fun a => ofList [a]⟩

instance : Insert α (FinSet α) where
  insert a s := Quotient.liftOn s (fun l => ofList (a :: l)) fun _ _ h =>
    ext fun x => by simp [h x]

instance : Union (FinSet α) where
  union s t := Quotient.liftOn₂ s t (fun l₁ l₂ => ofList (l₁ ++ l₂)) fun _ _ _ _ h₁ h₂ =>
    ext fun x => by simp [h₁ x, h₂ x]

instance [DecidableEq α] : Inter (FinSet α) where
  inter s t := Quotient.liftOn₂ s t (fun l₁ l₂ => ofList (l₁.filter (· ∈ l₂))) fun _ _ _ _ h₁ h₂ =>
    ext fun x => by simp [h₁ x, h₂ x]

instance [DecidableEq α] : SDiff (FinSet α) where
  sdiff s t := Quotient.liftOn₂ s t (fun l₁ l₂ => ofList (l₁.filter (· ∉ l₂))) fun _ _ _ _ h₁ h₂ =>
    ext fun x => by simp [h₁ x, h₂ x]

instance : HasSubset (FinSet α) := ⟨fun s t => ∀ x, x ∈ s → x ∈ t⟩

@[simp] theorem not_mem_empty (x : α) : x ∉ (∅ : FinSet α) := by
  simp [EmptyCollection.emptyCollection]

@[simp] theorem mem_singleton {x a : α} : x ∈ ({a} : FinSet α) ↔ x = a := by
  simp [Singleton.singleton]

@[simp] theorem mem_insert {x a : α} {s : FinSet α} : x ∈ insert a s ↔ x = a ∨ x ∈ s := by
  induction s using ind with | h l => exact (List.mem_cons : x ∈ a :: l ↔ _)

@[simp] theorem mem_union {x : α} {s t : FinSet α} : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by
  induction s using ind with | h l₁ => induction t using ind with | h l₂ =>
  exact (List.mem_append : x ∈ l₁ ++ l₂ ↔ _)

@[simp] theorem mem_inter [DecidableEq α] {x : α} {s t : FinSet α} : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t := by
  induction s using ind with | h l₁ => induction t using ind with | h l₂ =>
  show x ∈ l₁.filter (· ∈ l₂) ↔ _
  simp

@[simp] theorem mem_sdiff [DecidableEq α] {x : α} {s t : FinSet α} : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := by
  induction s using ind with | h l₁ => induction t using ind with | h l₂ =>
  show x ∈ l₁.filter (· ∉ l₂) ↔ _
  simp

theorem subset_def {s t : FinSet α} : s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t := Iff.rfl

@[simp] theorem ofList_eq_empty {l : List α} : ofList l = ∅ ↔ l = [] := by
  rw [ext_iff]
  simp only [mem_ofList, not_mem_empty, iff_false]
  exact ⟨fun h => List.eq_nil_iff_forall_not_mem.mpr h, fun h => by simp [h]⟩

@[simp] theorem ofArray_eq_empty {a : Array α} : ofArray a = ∅ ↔ a = #[] := by
  simp [ofArray, ofList_eq_empty]

instance [DecidableEq α] (x : α) (s : FinSet α) : Decidable (x ∈ s) :=
  Quotient.recOnSubsingleton s fun l => inferInstanceAs (Decidable (x ∈ l))

instance [DecidableEq α] (s t : FinSet α) : Decidable (s ⊆ t) :=
  Quotient.recOnSubsingleton₂ s t fun l₁ l₂ =>
    decidable_of_iff (∀ x ∈ l₁, x ∈ l₂) Iff.rfl

/-! ## Relations

A relation `Rel<A, B>` is a `FinSet (A × B)`. -/

section Relations

variable {β : Type v} {γ : Type w}

/-- The pairs `(a, c)` with `(a, b)` in `l₁` and `(b, c)` in `l₂`. -/
def joinList [DecidableEq β] (l₁ : List (α × β)) (l₂ : List (β × γ)) : List (α × γ) :=
  l₁.flatMap fun p => (l₂.filter (·.1 = p.2)).map fun q => (p.1, q.2)

theorem mem_joinList [DecidableEq β] {p : α × γ} {l₁ : List (α × β)} {l₂ : List (β × γ)} :
    p ∈ joinList l₁ l₂ ↔ ∃ b, (p.1, b) ∈ l₁ ∧ (b, p.2) ∈ l₂ := by
  constructor
  · simp only [joinList, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
    rintro ⟨⟨a, b⟩, h₁, ⟨b', c⟩, ⟨h₂, rfl⟩, rfl⟩
    exact ⟨_, h₁, h₂⟩
  · intro ⟨b, h₁, h₂⟩
    simp only [joinList, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨_, h₁, _, ⟨h₂, rfl⟩, rfl⟩

/-- The composition of two relations: `a` is related to `c` when some `b` links them. -/
def join [DecidableEq β] (r : FinSet (α × β)) (q : FinSet (β × γ)) : FinSet (α × γ) :=
  Quotient.liftOn₂ r q (fun l₁ l₂ => ofList (joinList l₁ l₂)) fun _ _ _ _ h₁ h₂ =>
    ext fun x => by simp [mem_joinList, h₁ _, h₂ _]

/-- The relation with each pair reversed. -/
def inverse (r : FinSet (α × β)) : FinSet (β × α) :=
  Quotient.liftOn r (fun l => ofList (l.map Prod.swap)) fun _ _ h =>
    ext fun x => by simp [h _]

/-- The first components of the pairs. -/
def domain (r : FinSet (α × β)) : FinSet α :=
  Quotient.liftOn r (fun l => ofList (l.map Prod.fst)) fun _ _ h =>
    ext fun x => by simp [h _]

/-- The second components of the pairs. -/
def range (r : FinSet (α × β)) : FinSet β :=
  Quotient.liftOn r (fun l => ofList (l.map Prod.snd)) fun _ _ h =>
    ext fun x => by simp [h _]

/-- The values related to some member of `s`. -/
def image [DecidableEq α] (r : FinSet (α × β)) (s : FinSet α) : FinSet β :=
  Quotient.liftOn₂ r s (fun l₁ l₂ => ofList ((l₁.filter (·.1 ∈ l₂)).map Prod.snd))
    fun _ _ _ _ h₁ h₂ => ext fun x => by simp [h₁ _, h₂ _]

@[simp] theorem mem_join [DecidableEq β] {r : FinSet (α × β)} {q : FinSet (β × γ)} {p : α × γ} :
    p ∈ join r q ↔ ∃ b, (p.1, b) ∈ r ∧ (b, p.2) ∈ q := by
  induction r using ind with | h l₁ => induction q using ind with | h l₂ =>
  exact mem_joinList

@[simp] theorem mem_inverse {r : FinSet (α × β)} {p : β × α} : p ∈ inverse r ↔ (p.2, p.1) ∈ r := by
  induction r using ind with | h l =>
  show p ∈ l.map Prod.swap ↔ _
  simp only [List.mem_map]
  exact ⟨fun ⟨q, h, e⟩ => e ▸ h, fun h => ⟨_, h, rfl⟩⟩

@[simp] theorem mem_domain {r : FinSet (α × β)} {a : α} : a ∈ domain r ↔ ∃ b, (a, b) ∈ r := by
  induction r using ind with | h l =>
  show a ∈ l.map Prod.fst ↔ _
  simp only [List.mem_map]
  exact ⟨fun ⟨⟨_, b⟩, h, e⟩ => ⟨b, e ▸ h⟩, fun ⟨_, h⟩ => ⟨_, h, rfl⟩⟩

@[simp] theorem mem_range {r : FinSet (α × β)} {b : β} : b ∈ range r ↔ ∃ a, (a, b) ∈ r := by
  induction r using ind with | h l =>
  show b ∈ l.map Prod.snd ↔ _
  simp only [List.mem_map]
  exact ⟨fun ⟨⟨a, _⟩, h, e⟩ => ⟨a, e ▸ h⟩, fun ⟨_, h⟩ => ⟨_, h, rfl⟩⟩

@[simp] theorem mem_image [DecidableEq α] {r : FinSet (α × β)} {s : FinSet α} {b : β} :
    b ∈ image r s ↔ ∃ a, a ∈ s ∧ (a, b) ∈ r := by
  induction r using ind with | h l₁ => induction s using ind with | h l₂ =>
  show b ∈ (l₁.filter (·.1 ∈ l₂)).map Prod.snd ↔ _
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨⟨a, _⟩, ⟨h, ha⟩, e⟩ => ⟨a, ha, e ▸ h⟩, fun ⟨_, ha, h⟩ => ⟨_, ⟨h, ha⟩, rfl⟩⟩

/-! ### Transitive closure

The closure is a fixpoint: starting from the pairs of `r`, add the pairs that
extend a pair by an edge of `r`, until there are none new. Every pair stays
within `square r`, the pairs of nodes of `r`, which bounds the number of steps. -/

/-- The pairs of nodes that appear in `l`. -/
def square (l : List (α × α)) : List (α × α) :=
  let nodes := l.map Prod.fst ++ l.map Prod.snd
  nodes.flatMap fun a => nodes.map fun b => (a, b)

theorem mem_square {l : List (α × α)} {p : α × α} :
    p ∈ square l ↔ p.1 ∈ l.map Prod.fst ++ l.map Prod.snd ∧ p.2 ∈ l.map Prod.fst ++ l.map Prod.snd := by
  simp only [square, List.mem_flatMap, List.mem_map]
  exact ⟨fun ⟨a, ha, b, hb, e⟩ => e ▸ ⟨ha, hb⟩, fun ⟨ha, hb⟩ => ⟨_, ha, _, hb, rfl⟩⟩

theorem joinList_mem_square [DecidableEq α] {l s : List (α × α)} (hs : ∀ p ∈ s, p ∈ square l)
    {p : α × α} (hp : p ∈ joinList s l) : p ∈ square l := by
  have ⟨b, h₁, h₂⟩ := mem_joinList.mp hp
  have h₁ := mem_square.mp (hs _ h₁)
  exact mem_square.mpr ⟨h₁.1, by simp only [List.mem_append, List.mem_map]; exact Or.inr ⟨_, h₂, rfl⟩⟩

/-- Extend `s` by edges of `l` until it is closed. -/
def closureLoop [DecidableEq α] (l s : List (α × α)) (hs : ∀ p ∈ s, p ∈ square l) : List (α × α) :=
  match h : (joinList s l).filter (· ∉ s) with
  | [] => s
  | x :: xs => closureLoop l (s ++ x :: xs) fun p hp => by
      rcases List.mem_append.mp hp with hp | hp
      · exact hs p hp
      · rw [← h] at hp; exact joinList_mem_square hs (List.mem_filter.mp hp).1
termination_by (square l).length - (nub s).length
decreasing_by
  have hx : x ∈ (joinList s l).filter (· ∉ s) := h ▸ List.mem_cons_self
  have hxs := (List.mem_filter.mp hx).2
  have hxs : x ∉ s := of_decide_eq_true hxs
  -- The new set has `x` and all of `s`, without repeats, and lies within the square.
  have h₁ := length_le_of_nodup (l₁ := x :: nub s) (l₂ := nub (s ++ x :: xs))
    (List.nodup_cons.mpr ⟨fun e => hxs (mem_nub.mp e), nodup_nub s⟩)
    fun y hy => mem_nub.mpr (by
      rcases List.mem_cons.mp hy with e | hy
      · exact List.mem_append_right _ (e ▸ List.mem_cons_self)
      · exact List.mem_append_left _ (mem_nub.mp hy))
  have h₂ := length_le_of_nodup (l₁ := nub (s ++ x :: xs)) (l₂ := square l) (nodup_nub _)
    fun y hy => by
      rcases List.mem_append.mp (mem_nub.mp hy) with hy | hy
      · exact hs y hy
      · rw [← h] at hy; exact joinList_mem_square hs (List.mem_filter.mp hy).1
  simp only [List.length_cons] at h₁
  omega

theorem closureLoop_spec [DecidableEq α] (l s : List (α × α)) (hs : ∀ p ∈ s, p ∈ square l) :
    (∀ p ∈ s, p ∈ closureLoop l s hs) ∧
    ((∀ p ∈ s, Relation.TransGen (fun x y => (x, y) ∈ l) p.1 p.2) →
      ∀ p ∈ closureLoop l s hs, Relation.TransGen (fun x y => (x, y) ∈ l) p.1 p.2) ∧
    (∀ a b c, (a, b) ∈ closureLoop l s hs → (b, c) ∈ l → (a, c) ∈ closureLoop l s hs) := by
  fun_induction closureLoop l s hs with
  | case1 s hs h =>
    refine ⟨fun _ => id, fun h => h, fun a b c hab hbc => ?_⟩
    have hj : (a, c) ∈ joinList s l := mem_joinList.mpr ⟨b, hab, hbc⟩
    have : (a, c) ∉ (joinList s l).filter (· ∉ s) := h ▸ List.not_mem_nil
    simpa [hj] using this
  | case2 s hs x xs h ih =>
    refine ⟨fun p hp => ih.1 p (List.mem_append_left _ hp), fun ht => ih.2.1 fun p hp => ?_, ih.2.2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact ht p hp
    · rw [← h] at hp
      have ⟨b, h₁, h₂⟩ := mem_joinList.mp (List.mem_filter.mp hp).1
      exact .tail (ht (p.1, b) h₁) h₂

theorem mem_square_of_mem {l : List (α × α)} {p : α × α} (hp : p ∈ l) : p ∈ square l :=
  mem_square.mpr
    ⟨List.mem_append_left _ (List.mem_map_of_mem hp), List.mem_append_right _ (List.mem_map_of_mem hp)⟩

/-- The transitive closure of `l`, as a list. -/
def closureList [DecidableEq α] (l : List (α × α)) : List (α × α) :=
  closureLoop l l fun _ => mem_square_of_mem

theorem mem_closureList [DecidableEq α] {l : List (α × α)} {a b : α} :
    (a, b) ∈ closureList l ↔ Relation.TransGen (fun x y => (x, y) ∈ l) a b := by
  have ⟨hsub, hgen, hclosed⟩ := closureLoop_spec l l fun _ => mem_square_of_mem
  refine ⟨fun h => hgen (fun p hp => .single hp) _ h, fun h => ?_⟩
  induction h with
  | single h => exact hsub _ h
  | tail _ h ih => exact hclosed _ _ _ ih h

/-- The transitive closure: `(a, b)` when a path of one or more pairs leads from `a` to `b`. -/
def closure [DecidableEq α] (r : FinSet (α × α)) : FinSet (α × α) :=
  Quotient.liftOn r (fun l => ofList (closureList l)) fun l₁ l₂ h => by
    have e : (fun x y => (x, y) ∈ l₁) = (fun x y => (x, y) ∈ l₂) :=
      funext fun x => funext fun y => propext (h (x, y))
    exact ext fun ⟨a, b⟩ => by simp only [mem_ofList, mem_closureList, e]

theorem mem_closure [DecidableEq α] {r : FinSet (α × α)} {a b : α} :
    (a, b) ∈ closure r ↔ Relation.TransGen (fun x y => (x, y) ∈ r) a b := by
  induction r using ind with | h l => exact mem_closureList

end Relations

/-- The members, in the order of some list of them. -/
unsafe def toListUnsafe (s : FinSet α) : List α := unsafeCast s

@[implemented_by toListUnsafe] opaque toListImpl (s : FinSet α) : List α

instance [Repr α] : Repr (FinSet α) where
  reprPrec s _ := "{" ++ ", ".intercalate ((toListImpl s).map fun a => (repr a).pretty) ++ "}"

instance [DecidableEq α] : DecidableEq (FinSet α) := fun s t =>
  decidable_of_iff (s ⊆ t ∧ t ⊆ s) ⟨fun ⟨h₁, h₂⟩ => ext fun x => ⟨h₁ x, h₂ x⟩, fun h => h ▸ ⟨fun _ => id, fun _ => id⟩⟩

end FinSet

end Fren
