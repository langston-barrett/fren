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

/-- Map over a snoc-list. -/
def mapS {α β : Type} (f : α → β) : Snoc α → Snoc β
  | .Empty => .Empty
  | .Extend earlier x => .Extend (mapS f earlier) (f x)

/-- The elements of a snoc-list, last first. -/
def toList {α : Type} : Snoc α → List α
  | .Empty => []
  | .Extend earlier x => x :: toList earlier

theorem mapS_id {α : Type} (xs : Snoc α) : mapS (fun x => x) xs = xs := by
  induction xs with
  | Empty => rfl
  | Extend e x ih => simp [mapS, ih]

theorem mapS_mapS {α β γ : Type} (f : α → β) (g : β → γ) (xs : Snoc α) :
    mapS g (mapS f xs) = mapS (fun x => g (f x)) xs := by
  induction xs with
  | Empty => rfl
  | Extend e x ih => simp [mapS, ih]

theorem toList_mapS {α β : Type} (f : α → β) (xs : Snoc α) :
    toList (mapS f xs) = (toList xs).map f := by
  induction xs with
  | Empty => rfl
  | Extend e x ih => simp [mapS, toList, ih]

theorem mapS_congr {α β : Type} (f g : α → β) (xs : Snoc α)
    (h : ∀ c ∈ toList xs, f c = g c) : mapS f xs = mapS g xs := by
  induction xs with
  | Empty => rfl
  | Extend e x ih =>
    simp only [mapS]
    rw [ih (fun c hc => h c (List.mem_cons_of_mem _ hc)), h x List.mem_cons_self]

theorem mapS_zip {α β γ : Type} (f : α → γ) (g : β → γ) (xs : Snoc α) :
    ∀ ys : Snoc β, mapS f xs = mapS g ys →
      ∃ zs : Snoc (α × β), mapS Prod.fst zs = xs ∧ mapS Prod.snd zs = ys ∧
        ∀ c ∈ toList zs, f c.1 = g c.2 := by
  induction xs with
  | Empty =>
    intro ys h
    cases ys with
    | Empty => exact ⟨.Empty, rfl, rfl, fun _ hc => nomatch hc⟩
    | Extend _ _ => simp [mapS] at h
  | Extend e x ih =>
    intro ys h
    cases ys with
    | Empty => simp [mapS] at h
    | Extend e' y =>
      simp only [mapS, Snoc.Extend.injEq] at h
      obtain ⟨zs, h1, h2, h3⟩ := ih e' h.1
      refine ⟨.Extend zs (x, y), by simp [mapS, h1], by simp [mapS, h2], ?_⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h.2
      · exact h3 c hc

/-- Map over the subexpressions of one layer. -/
def mapArm {α β : Type} (f : α → β) (arm : ArmF α) : ArmF β := ⟨arm.constructor, f arm.body⟩

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
  | .Unary _ x => [x]
  | .Binary _ x y => [x, y]
  | .Call _ args => toList args
  | .Let _ value body => [value, body]
  | .If c t e => [c, t, e]
  | .Match scrutinee arms => scrutinee :: (toList arms).map (·.body)
  | _ => []

theorem mapF_zip {α β γ : Type} (f : α → γ) (g : β → γ) (l : CoreF α) (m : CoreF β)
    (h : mapF f l = mapF g m) :
    ∃ z : CoreF (α × β), mapF Prod.fst z = l ∧ mapF Prod.snd z = m ∧
      ∀ c ∈ childrenF z, f c.1 = g c.2 := by
  cases l <;> cases m <;> simp only [mapF, reduceCtorEq, CoreF.BooleanLiteral.injEq,
    CoreF.IntegerLiteral.injEq, CoreF.Local.injEq, CoreF.Constructor.injEq, CoreF.Unary.injEq,
    CoreF.Binary.injEq, CoreF.Call.injEq, CoreF.Let.injEq, CoreF.If.injEq,
    CoreF.Match.injEq] at h
  case BooleanLiteral.BooleanLiteral b _ => subst h; exact ⟨.BooleanLiteral b, rfl, rfl, by simp [childrenF]⟩
  case IntegerLiteral.IntegerLiteral b _ => subst h; exact ⟨.IntegerLiteral b, rfl, rfl, by simp [childrenF]⟩
  case Local.Local b _ => subst h; exact ⟨.Local b, rfl, rfl, by simp [childrenF]⟩
  case Constructor.Constructor b _ => subst h; exact ⟨.Constructor b, rfl, rfl, by simp [childrenF]⟩
  case Unary.Unary op x _ y =>
    obtain ⟨rfl, hx⟩ := h
    exact ⟨.Unary op (x, y), rfl, rfl, by simp [childrenF, hx]⟩
  case Binary.Binary op x1 x2 _ y1 y2 =>
    obtain ⟨rfl, h1, h2⟩ := h
    exact ⟨.Binary op (x1, y1) (x2, y2), rfl, rfl, by simp [childrenF, h1, h2]⟩
  case Call.Call item xs _ ys =>
    obtain ⟨rfl, hs⟩ := h
    obtain ⟨zs, h1, h2, h3⟩ := mapS_zip f g xs ys hs
    exact ⟨.Call item zs, by simp [mapF, h1], by simp [mapF, h2], h3⟩
  case Let.Let ann x1 x2 _ y1 y2 =>
    obtain ⟨rfl, h1, h2⟩ := h
    exact ⟨.Let ann (x1, y1) (x2, y2), rfl, rfl, by simp [childrenF, h1, h2]⟩
  case If.If x1 x2 x3 y1 y2 y3 =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨.If (x1, y1) (x2, y2) (x3, y3), rfl, rfl, by simp [childrenF, h1, h2, h3]⟩
  case Match.Match x xs y ys =>
    obtain ⟨hx, hs⟩ := h
    obtain ⟨zs, h1, h2, h3⟩ := mapS_zip (mapArm f) (mapArm g) xs ys hs
    have hk : ∀ c ∈ toList zs, c.1.constructor = c.2.constructor ∧ f c.1.body = g c.2.body := by
      intro c hc
      have := h3 c hc
      simp only [mapArm, ArmF.mk!.injEq] at this
      exact this
    refine ⟨.Match (x, y) (mapS (fun c => ⟨c.1.constructor, (c.1.body, c.2.body)⟩) zs), ?_, ?_, ?_⟩
    · simp only [mapF, mapS_mapS, mapArm]
      rw [← h1]
    · simp only [mapF, mapS_mapS, mapArm]
      rw [← h2]
      congr 1
      apply mapS_congr
      intro c hc
      rw [(hk c hc).1]
    · intro c hc
      simp only [childrenF, toList_mapS, List.map_map, List.mem_cons, List.mem_map,
        Function.comp] at hc
      rcases hc with rfl | ⟨c0, hc0, rfl⟩
      · exact hx
      · exact (hk c0 hc0).2

instance : Layer CoreF where
  map := mapF
  children := childrenF
  map_id l := by
    cases l <;> simp [mapF, mapS_id]
    exact mapS_id _
  map_map f g l := by
    cases l <;> simp [mapF, mapS_mapS, mapArm] <;> rfl
  children_map f l := by
    cases l <;> simp [mapF, childrenF, toList_mapS, mapArm, Function.comp_def]
  map_congr f g l h := by
    cases l with
    | BooleanLiteral _ | IntegerLiteral _ | Local _ | Constructor _ => rfl
    | Unary op x => simp [mapF, h x (by simp [childrenF])]
    | Binary op x y => simp [mapF, h x (by simp [childrenF]), h y (by simp [childrenF])]
    | Call item args => simp only [mapF]; rw [mapS_congr f g args h]
    | Let ann x y => simp [mapF, h x (by simp [childrenF]), h y (by simp [childrenF])]
    | If x y z =>
      simp [mapF, h x (by simp [childrenF]), h y (by simp [childrenF]), h z (by simp [childrenF])]
    | Match x arms =>
      simp only [mapF]
      rw [h x (by simp [childrenF]), mapS_congr (mapArm f) (mapArm g) arms (fun c hc => by
        simp only [mapArm]
        rw [h c.body (by simp only [childrenF]; exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨c, hc, rfl⟩))])]
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
