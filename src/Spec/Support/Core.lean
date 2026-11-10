import Spec.Support.Tables

/-!
# Core expressions as trees

`CoreF` is the one layer of a Core expression. This module makes it a
`Spec.Tables.Layer` and ties the knot: `Core` is the type of whole Core
expressions, which Fren cannot define. A chapter whose tables have `CoreF`
forms unfolds them to `Core` terms with `Spec.Tables`.
-/

open Fren.Lang
open spec.surface spec.names

namespace Spec.Tables

/-! ## Snoc-lists

Simp-normal forms. `mapS` and `toList` compute on `Empty` and `Extend`.
Maps fuse into one map (`mapS_mapS`) and the identity map vanishes
(`mapS_id`). `toList` moves inward past a map (`toList_mapS`), so that
membership in a mapped list is `List.mem_map`. No lemma here is tagged in
both directions, and none grows its term. -/

/-- Map over a snoc-list. -/
@[simp] def mapS {α β : Type} (f : α → β) : Snoc α → Snoc β
  | .Empty => .Empty
  | .Extend earlier x => .Extend (mapS f earlier) (f x)

/-- The elements of a snoc-list, last first. -/
@[simp] def toList {α : Type} : Snoc α → List α
  | .Empty => []
  | .Extend earlier x => x :: toList earlier

@[simp] theorem mapS_id {α : Type} (xs : Snoc α) : mapS (fun x => x) xs = xs := by
  induction xs <;> simp [*]

@[simp] theorem mapS_mapS {α β γ : Type} (f : α → β) (g : β → γ) (xs : Snoc α) :
    mapS g (mapS f xs) = mapS (fun x => g (f x)) xs := by
  induction xs <;> simp [*]

@[simp] theorem toList_mapS {α β : Type} (f : α → β) (xs : Snoc α) :
    toList (mapS f xs) = (toList xs).map f := by
  induction xs <;> simp [*]

theorem mapS_congr {α β : Type} (f g : α → β) (xs : Snoc α)
    (h : ∀ c ∈ toList xs, f c = g c) : mapS f xs = mapS g xs := by
  induction xs with
  | Empty => rfl
  | Extend e x ih =>
    simp only [mapS]
    rw [ih (fun c hc => h c (List.mem_cons_of_mem _ hc)), h x List.mem_cons_self]

/-- Snoc-lists with equal images are the two projections of one snoc-list of
pairs whose components have equal images. -/
theorem mapS_zip {α β γ : Type} (f : α → γ) (g : β → γ) (xs : Snoc α) :
    ∀ ys : Snoc β, mapS f xs = mapS g ys →
      ∃ zs : Snoc (α × β), mapS Prod.fst zs = xs ∧ mapS Prod.snd zs = ys ∧
        ∀ c ∈ toList zs, f c.1 = g c.2 := by
  induction xs with
  | Empty =>
    intro ys h
    cases ys with
    | Empty => exact ⟨.Empty, rfl, rfl, fun _ hc => nomatch hc⟩
    | Extend _ _ => nomatch h
  | Extend e x ih =>
    intro ys h
    cases ys with
    | Empty => nomatch h
    | Extend e' y =>
      simp only [mapS, Snoc.Extend.injEq] at h
      obtain ⟨zs, rfl, rfl, h3⟩ := ih e' h.1
      exact ⟨.Extend zs (x, y), rfl, rfl, List.forall_mem_cons.2 ⟨h.2, h3⟩⟩

/-! ## One layer of a Core expression

Simp-normal forms. `mapF`, `childrenF` and `mapArm` compute on constructors.
Maps fuse (`mapF_mapF`, `mapArm_mapArm`) and identity maps vanish
(`mapF_id`, `mapArm_id`). `childrenF` moves inward past a map
(`childrenF_mapF`). At `CoreF`, `simp` reduces `Layer.map` and
`Layer.children` to `mapF` and `childrenF`, so these are the forms that
lemmas about Core expressions state. -/

/-- Map over the body of a match arm. -/
def mapArm {α β : Type} (f : α → β) (arm : ArmF α) : ArmF β := ⟨arm.constructor, f arm.body⟩

@[simp] theorem mapArm_constructor {α β : Type} (f : α → β) (arm : ArmF α) :
    (mapArm f arm).constructor = arm.constructor := rfl

@[simp] theorem mapArm_body {α β : Type} (f : α → β) (arm : ArmF α) :
    (mapArm f arm).body = f arm.body := rfl

@[simp] theorem mapArm_mk {α β : Type} (f : α → β) (c) (b : α) :
    mapArm f (ArmF.mk! c b) = ArmF.mk! c (f b) := rfl

@[simp] theorem mapArm_id {α : Type} : mapArm (fun x : α => x) = fun arm => arm := rfl

@[simp] theorem mapArm_mapArm {α β γ : Type} (f : α → β) (g : β → γ) (arm : ArmF α) :
    mapArm g (mapArm f arm) = mapArm (fun x => g (f x)) arm := rfl

/-- Map over the subexpressions of one layer. -/
def mapF {α β : Type} (f : α → β) : CoreF α → CoreF β
  | .BooleanLiteral b => .BooleanLiteral b
  | .IntegerLiteral n => .IntegerLiteral n
  | .Local level => .Local level
  | .Constructor item => .Constructor item
  | .Unary op x => .Unary op (f x)
  | .Binary op x y => .Binary op (f x) (f y)
  | .Call item args => .Call item (mapS f args)
  | .Let annotation value body => .Let annotation (f value) (f body)
  | .If c t e => .If (f c) (f t) (f e)
  | .Match scrutinee arms => .Match (f scrutinee) (mapS (mapArm f) arms)

/-- The subexpressions of one layer. -/
def childrenF {α : Type} : CoreF α → List α
  | .BooleanLiteral _ | .IntegerLiteral _ | .Local _ | .Constructor _ => []
  | .Unary _ x => [x]
  | .Binary _ x y => [x, y]
  | .Call _ args => toList args
  | .Let _ value body => [value, body]
  | .If c t e => [c, t, e]
  | .Match scrutinee arms => scrutinee :: (toList arms).map (·.body)

/- The equations of `mapF` and `childrenF`, one for each constructor. `@[simp]`
on the definitions would instead unfold them at a variable layer, to a `match`
that no lemma below applies to. -/
attribute [simp] mapF.eq_1 mapF.eq_2 mapF.eq_3 mapF.eq_4 mapF.eq_5 mapF.eq_6 mapF.eq_7 mapF.eq_8
  mapF.eq_9 mapF.eq_10 childrenF.eq_1 childrenF.eq_2 childrenF.eq_3 childrenF.eq_4 childrenF.eq_5
  childrenF.eq_6 childrenF.eq_7 childrenF.eq_8 childrenF.eq_9 childrenF.eq_10

@[simp] theorem mapF_id {α : Type} (l : CoreF α) : mapF (fun x => x) l = l := by
  cases l <;> simp

@[simp] theorem mapF_mapF {α β γ : Type} (f : α → β) (g : β → γ) (l : CoreF α) :
    mapF g (mapF f l) = mapF (fun x => g (f x)) l := by
  cases l <;> simp

@[simp] theorem childrenF_mapF {α β : Type} (f : α → β) (l : CoreF α) :
    childrenF (mapF f l) = (childrenF l).map f := by
  cases l <;> simp [Function.comp_def]

theorem mapF_congr {α β : Type} (f g : α → β) (l : CoreF α)
    (h : ∀ c ∈ childrenF l, f c = g c) : mapF f l = mapF g l := by
  cases l with
  | Call item args => simp [mapS_congr f g args h]
  | Match x arms =>
    have hx : f x = g x := h x (by simp)
    have harms : mapS (mapArm f) arms = mapS (mapArm g) arms :=
      mapS_congr _ _ arms fun arm hm => by
        simp [mapArm, h arm.body
          (by simp only [childrenF]; exact .tail _ (List.mem_map.2 ⟨arm, hm, rfl⟩))]
    simp [hx, harms]
  | _ => simp_all

/-- Layers with equal images are the two projections of one layer of pairs
whose components have equal images. -/
theorem mapF_zip {α β γ : Type} (f : α → γ) (g : β → γ) (l : CoreF α) (m : CoreF β)
    (h : mapF f l = mapF g m) :
    ∃ z : CoreF (α × β), mapF Prod.fst z = l ∧ mapF Prod.snd z = m ∧
      ∀ c ∈ childrenF z, f c.1 = g c.2 := by
  cases l <;> cases m <;> simp only [mapF, reduceCtorEq, CoreF.BooleanLiteral.injEq,
    CoreF.IntegerLiteral.injEq, CoreF.Local.injEq, CoreF.Constructor.injEq, CoreF.Unary.injEq,
    CoreF.Binary.injEq, CoreF.Call.injEq, CoreF.Let.injEq, CoreF.If.injEq,
    CoreF.Match.injEq] at h
  case BooleanLiteral.BooleanLiteral b _ => exact ⟨.BooleanLiteral b, by simp [h]⟩
  case IntegerLiteral.IntegerLiteral b _ => exact ⟨.IntegerLiteral b, by simp [h]⟩
  case Local.Local b _ => exact ⟨.Local b, by simp [h]⟩
  case Constructor.Constructor b _ => exact ⟨.Constructor b, by simp [h]⟩
  case Unary.Unary op x _ y => exact ⟨.Unary op (x, y), by simp [h]⟩
  case Binary.Binary op x1 x2 _ y1 y2 => exact ⟨.Binary op (x1, y1) (x2, y2), by simp [h]⟩
  case Call.Call item xs _ ys =>
    obtain ⟨rfl, hs⟩ := h
    obtain ⟨zs, rfl, rfl, h3⟩ := mapS_zip f g xs ys hs
    exact ⟨.Call item zs, rfl, rfl, h3⟩
  case Let.Let ann x1 x2 _ y1 y2 => exact ⟨.Let ann (x1, y1) (x2, y2), by simp [h]⟩
  case If.If x1 x2 x3 y1 y2 y3 => exact ⟨.If (x1, y1) (x2, y2) (x3, y3), by simp [h]⟩
  case Match.Match x xs y ys =>
    obtain ⟨zs, rfl, rfl, h3⟩ := mapS_zip (mapArm f) (mapArm g) xs ys h.2
    have hk : ∀ c ∈ toList zs, c.1.constructor = c.2.constructor ∧ f c.1.body = g c.2.body :=
      fun c hc => by simpa only [mapArm, ArmF.mk!.injEq] using h3 c hc
    refine ⟨.Match (x, y) (mapS (fun c => ⟨c.1.constructor, (c.1.body, c.2.body)⟩) zs),
      by simp [mapArm], ?_, ?_⟩
    · simp only [mapF, mapS_mapS]
      exact congrArg _ (mapS_congr _ _ zs fun c hc => by simp [mapArm, (hk c hc).1])
    · intro c hc
      simp only [childrenF, toList_mapS, List.map_map, List.mem_cons, List.mem_map,
        Function.comp] at hc
      rcases hc with rfl | ⟨c0, hc0, rfl⟩
      · exact h.1
      · exact (hk c0 hc0).2

/-- `CoreF` is a layer. Its laws are the simp lemmas above. -/
instance : Layer CoreF where
  map := mapF
  children := childrenF
  map_id := mapF_id
  map_map := mapF_mapF
  children_map := childrenF_mapF
  map_congr := mapF_congr
  zip := mapF_zip

/-- A Core expression: a tree whose every layer is a `CoreF`. -/
inductive Core : Type
  | mk : CoreF Core → Core

instance : Nonempty Core := ⟨.mk (.BooleanLiteral true)⟩

/-- `shift_form` at any child type: it shifts a local and changes no other
form. -/
def shiftF (cutoff : Int) (α : Type) : CoreF α → CoreF α
  | .Local level => .Local (shift level cutoff)
  | l => l

theorem shiftF_form (cutoff : Int) (form : CoreF Int) :
    shiftF cutoff Int form = shift_form form cutoff := by
  cases form <;> simp [shiftF, shift_form, fren_spec]

theorem shiftF_natural (cutoff : Int) {α β : Type} (f : α → β) (l : CoreF α) :
    mapF f (shiftF cutoff α l) = shiftF cutoff β (mapF f l) := by
  cases l <;> rfl

theorem shiftF_within (cutoff : Int) {α : Type} (l : CoreF α) :
    ∀ c ∈ childrenF (shiftF cutoff α l), c ∈ childrenF l := by
  cases l <;> exact fun _ h => h

end Spec.Tables
