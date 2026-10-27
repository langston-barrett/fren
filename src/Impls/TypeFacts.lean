-- keep-sorted start
import FrenCore.TypeFacts
import Impls.Lang
-- keep-sorted end
open Fren.Lang

/-!
# Facts of types over their constituents (`Reqs/Lang/Types#finite-types`)

The procedures that use the facts of a type closed over its constituents
(`lang::type_facts`), proved against `Fren.Core.typeFacts`, which both
front ends call. The constituent relation is the one that
`Fren.Core.Node.next` gives from the declarations, over every type that the
type is built from, and the proofs hold for every type and declarations
whose facts are known: where the facts are unknown, `typeFacts` gives the
ones that accept the least (`Fren.Core.TypeFacts.unknown`).
-/

namespace Fren.Impls

open Fren.Core (Node DataShape)

interp lang::DeclaredTy := Fren.Core.Node

interp lang::declared_kind := fun (n : Fren.Core.Node) => kindOf n.ty

interp lang::pattern_bounded? := Fren.Core.Node.bounded

/-! ## Closures -/

theorem transGen_iff_head {α : Type} {r : α → α → Prop} {a c : α} :
    Relation.TransGen r a c ↔ ∃ b, r a b ∧ (c = b ∨ Relation.TransGen r b c) := by
  constructor
  · intro h
    induction h with
    | single h => exact ⟨_, h, .inl rfl⟩
    | tail _ hbc ih =>
      obtain ⟨b, hab, hb⟩ := ih
      refine ⟨b, hab, .inr ?_⟩
      rcases hb with rfl | hb
      · exact .single hbc
      · exact .tail hb hbc
  · rintro ⟨b, hab, rfl | hb⟩
    · exact .single hab
    · exact Relation.TransGen.trans (.single hab) hb

section Chain

variable {α : Type}

/-- A type's chain is the type and what the chain of each of the types it
relates to has (`lang::chain`). -/
theorem mem_chain {C : FinSet (α × α)} {t u : α} :
    u ∈ lang.chain α t C ↔ u = t ∨ ∃ v, (t, v) ∈ C ∧ u ∈ lang.chain α v C := by
  simp only [lang.chain, FinSet.mem_union, FinSet.mem_image, FinSet.mem_singleton,
    FinSet.mem_closure, exists_eq_left]
  rw [transGen_iff_head]
  constructor
  · rintro (⟨v, hv, h⟩ | rfl)
    · exact .inr ⟨v, hv, h.symm⟩
    · exact .inl rfl
  · rintro (rfl | ⟨v, hv, h⟩)
    · exact .inr rfl
    · exact .inl ⟨v, hv, h.symm⟩

theorem exists_chain {C : FinSet (α × α)} {t : α} {p : α → Prop} :
    (∃ u, u ∈ lang.chain α t C ∧ p u) ↔ p t ∨ ∃ v, (t, v) ∈ C ∧ ∃ u, u ∈ lang.chain α v C ∧ p u := by
  constructor
  · rintro ⟨u, hu, hp⟩
    rcases mem_chain.mp hu with rfl | ⟨v, hc, hu⟩
    · exact .inl hp
    · exact .inr ⟨v, hc, u, hu, hp⟩
  · rintro (hp | ⟨v, hc, u, hu, hp⟩)
    · exact ⟨t, mem_chain.mpr (.inl rfl), hp⟩
    · exact ⟨u, mem_chain.mpr (.inr ⟨v, hc, hu⟩), hp⟩

end Chain

/-! ## The closure that `Fren.Core.reach` computes -/

section Reach

variable (next : Node → Option (List Node))

/-- `v` is a constituent of `u`, by `next`. -/
def Step (u v : Node) : Prop := ∃ l, next u = some l ∧ v ∈ l

/-- `b` is `a`, or the closure of `Step` reaches it from `a`. -/
def Reaches (a b : Node) : Prop := a = b ∨ Relation.TransGen (Step next) a b

theorem Reaches.head {next : Node → Option (List Node)} {a b c : Node} (h : Step next a b) (r : Reaches next b c) :
    Reaches next a c :=
  .inr (r.elim (fun e => e ▸ .single h) fun r => Relation.TransGen.trans (.single h) r)

theorem Reaches.tail {next : Node → Option (List Node)} {a b c : Node} (r : Reaches next a b) (h : Step next b c) :
    Reaches next a c :=
  .inr (r.elim (fun e => e ▸ .single h) fun r => .tail r h)

/-- Every node of `S` has its constituents, and they are in `S`. -/
def Closed (S : List Node) : Prop := ∀ s ∈ S, ∃ l, next s = some l ∧ ∀ v ∈ l, v ∈ S

theorem reach_spec : ∀ (fuel : Nat) (todo seen S : List Node), Fren.Core.reach next fuel todo seen = some S →
    (∀ s ∈ seen, ∃ l, next s = some l ∧ ∀ v ∈ l, v ∈ seen ∨ v ∈ todo) →
    (∀ x, x ∈ seen ∨ x ∈ todo → x ∈ S) ∧ Closed next S ∧
    (∀ x ∈ S, x ∈ seen ∨ ∃ y ∈ todo, Reaches next y x)
  | _, [], seen, S, h, hi => by
    simp only [Fren.Core.reach, Option.some.injEq] at h
    subst h
    refine ⟨fun x hx => hx.elim id (by simp), fun s hs => ?_, fun x hx => .inl hx⟩
    obtain ⟨l, hl, hv⟩ := hi s hs
    exact ⟨l, hl, fun v hv' => (hv v hv').elim id (by simp)⟩
  | 0, _ :: _, _, _, h, _ => by simp [Fren.Core.reach] at h
  | fuel + 1, t :: todo, seen, S, h, hi => by
    simp only [Fren.Core.reach] at h
    split at h
    · rename_i ht
      obtain ⟨ha, hc, hs⟩ := reach_spec fuel todo seen S h fun s hs => by
        obtain ⟨l, hl, hv⟩ := hi s hs
        refine ⟨l, hl, fun v hv' => ?_⟩
        rcases hv v hv' with h | h
        · exact .inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact .inl ht
          · exact .inr h
      refine ⟨fun x hx => ha x ?_, hc, fun x hx => ?_⟩
      · rcases hx with h | h
        · exact .inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact .inl ht
          · exact .inr h
      · rcases hs x hx with h | ⟨y, hy, hr⟩
        · exact .inl h
        · exact .inr ⟨y, List.mem_cons_of_mem _ hy, hr⟩
    · rename_i ht
      cases hn : next t with
      | none => simp [hn] at h
      | some ns =>
        simp only [hn, Option.bind_eq_bind, Option.bind_some] at h
        obtain ⟨ha, hc, hs⟩ := reach_spec fuel (ns ++ todo) (t :: seen) S h fun s hs => by
          rcases List.mem_cons.mp hs with rfl | hs
          · exact ⟨ns, hn, fun v hv => .inr (List.mem_append_left _ hv)⟩
          · obtain ⟨l, hl, hv⟩ := hi s hs
            refine ⟨l, hl, fun v hv' => ?_⟩
            rcases hv v hv' with h | h
            · exact .inl (List.mem_cons_of_mem _ h)
            · rcases List.mem_cons.mp h with rfl | h
              · exact .inl (List.mem_cons_self ..)
              · exact .inr (List.mem_append_right _ h)
        refine ⟨fun x hx => ha x ?_, hc, fun x hx => ?_⟩
        · rcases hx with h | h
          · exact .inl (List.mem_cons_of_mem _ h)
          · rcases List.mem_cons.mp h with rfl | h
            · exact .inl (List.mem_cons_self ..)
            · exact .inr (List.mem_append_right _ h)
        · rcases hs x hx with h | ⟨y, hy, hr⟩
          · rcases List.mem_cons.mp h with rfl | h
            · exact .inr ⟨x, List.mem_cons_self .., .inl rfl⟩
            · exact .inl h
          · rcases List.mem_append.mp hy with hy | hy
            · exact .inr ⟨t, List.mem_cons_self .., Reaches.head ⟨ns, hn, hy⟩ hr⟩
            · exact .inr ⟨y, List.mem_cons_of_mem _ hy, hr⟩

theorem mem_of_closed {S : List Node} (hc : Closed next S) {a b : Node} (ha : a ∈ S)
    (h : Reaches next a b) : b ∈ S := by
  rcases h with rfl | h
  · exact ha
  induction h with
  | single hs =>
    obtain ⟨l, hl, hv⟩ := hc _ ha
    obtain ⟨l', hl', hb⟩ := hs
    rw [hl] at hl'
    cases hl'
    exact hv _ hb
  | tail _ hs ih =>
    obtain ⟨l, hl, hv⟩ := hc _ ih
    obtain ⟨l', hl', hb⟩ := hs
    rw [hl] at hl'
    cases hl'
    exact hv _ hb

/-- What `reach` gives from `todo`, with nothing visited: every node that
the closure reaches from `todo`, and a closed list. -/
theorem reach_eq {fuel : Nat} {todo S : List Node} (h : Fren.Core.reach next fuel todo [] = some S) :
    (∀ x, x ∈ S ↔ ∃ y ∈ todo, Reaches next y x) ∧ Closed next S := by
  obtain ⟨ha, hc, hs⟩ := reach_spec next fuel todo [] S h (by simp)
  refine ⟨fun x => ⟨fun hx => (hs x hx).elim (by simp) id, ?_⟩, hc⟩
  rintro ⟨y, hy, hr⟩
  exact mem_of_closed next hc (ha y (.inr hy)) hr

/-- The pairs of a node of `S` and one of its constituents. -/
def edges (S : List Node) : List (Node × Node) := S.flatMap fun u => ((next u).getD []).map (u, ·)

theorem mem_edges {S : List Node} {a b : Node} : (a, b) ∈ edges next S ↔ a ∈ S ∧ b ∈ (next a).getD [] := by
  simp only [edges, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨u, hu, v, hv, rfl, rfl⟩
    exact ⟨hu, hv⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, rfl, rfl⟩

/-- Over the pairs of a closed `S`, the closure from a node of `S` is the
closure of `Step`. -/
theorem transGen_edges {S : List Node} (hc : Closed next S) {a b : Node} (ha : a ∈ S) :
    Relation.TransGen (fun x y => (x, y) ∈ edges next S) a b ↔ Relation.TransGen (Step next) a b := by
  have step : ∀ x y, x ∈ S → ((x, y) ∈ edges next S ↔ Step next x y) := fun x y hx => by
    obtain ⟨l, hl, _⟩ := hc x hx
    rw [mem_edges]
    simp [Step, hl, hx]
  constructor
  · intro h
    induction h with
    | single h => exact .single ((step _ _ (mem_edges next |>.mp h).1).mp h)
    | tail _ h ih => exact .tail ih ((step _ _ (mem_edges next |>.mp h).1).mp h)
  · intro h
    induction h with
    | single h => exact .single ((step _ _ ha).mpr h)
    | tail h₁ h ih =>
      have hm := mem_of_closed next hc ha (.inr h₁)
      exact .tail ih ((step _ _ hm).mpr h)

end Reach

/-! ## The facts (`lang::type_facts`) -/

/-- The nodes that `t` is built from, by the declarations `shapes`. -/
def builtOf (shapes : Lean.Name → Option DataShape) (t : Node) : List Node :=
  (Fren.Core.reach (Node.next shapes) Fren.Core.reachFuel [t] []).getD []

/-- The constituent relation over the nodes that `t` is built from. -/
def constituentsOf (shapes : Lean.Name → Option DataShape) (t : Node) : FinSet (Node × Node) :=
  FinSet.ofList (edges (Node.next shapes) (builtOf shapes t))

theorem recursive?_spec {shapes : Lean.Name → Option DataShape} {u : Node} {b : Bool}
    (h : Fren.Core.recursive? shapes u = some b) :
    b = true ↔ Relation.TransGen (Step (Node.next shapes)) u u := by
  simp only [Fren.Core.recursive?, Option.bind_eq_bind] at h
  cases hn : Node.next shapes u with
  | none => simp [hn] at h
  | some ns =>
    cases hr : Fren.Core.reach (Node.next shapes) Fren.Core.reachFuel ns [] with
    | none => simp [hn, hr] at h
    | some r =>
      simp only [hn, hr, Option.bind_some, Option.some.injEq] at h
      subst h
      rw [List.contains_iff_mem, (reach_eq _ hr).1, transGen_iff_head]
      constructor
      · rintro ⟨y, hy, hr⟩
        exact ⟨y, ⟨ns, hn, hy⟩, hr.imp Eq.symm id⟩
      · rintro ⟨y, ⟨l, hl, hy⟩, hr⟩
        rw [hn] at hl
        cases hl
        exact ⟨y, hy, hr.imp Eq.symm id⟩

/-- When the facts of `u` are known, they are the closure's, over any
closed list of nodes that holds `u`. -/
theorem typeFacts_spec {shapes : Lean.Name → Option DataShape} {u : Node} {F : Fren.Core.TypeFacts}
    (h : Fren.Core.typeFacts? shapes u = some F) :
    (F.recursive = true ↔ Relation.TransGen (Step (Node.next shapes)) u u) ∧
    (F.finite = true ↔ ∀ w, Reaches (Node.next shapes) u w →
      w.former.finite = true ∧ ¬Relation.TransGen (Step (Node.next shapes)) w w) ∧
    (F.unbounded = true ↔ ∃ w, Reaches (Node.next shapes) u w ∧
      (w.former.growing = true ∨ Relation.TransGen (Step (Node.next shapes)) w w)) := by
  simp only [Fren.Core.typeFacts?, Option.bind_eq_bind] at h
  cases hb : Fren.Core.reach (Node.next shapes) Fren.Core.reachFuel [u] [] with
  | none => simp [hb] at h
  | some S =>
    simp only [hb, Option.bind_some] at h
    split at h
    · rename_i hall
      simp only [Option.some.injEq] at h
      subst h
      have hS := (reach_eq _ hb).1
      have hrec : ∀ w ∈ S, ((Fren.Core.recursive? shapes w).getD true = true ↔
          Relation.TransGen (Step (Node.next shapes)) w w) := fun w hw => by
        have hs : (Fren.Core.recursive? shapes w).isSome = true := by
          have := List.all_eq_true.mp hall w hw
          simpa using this
        obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.mp hs
        rw [hb', Option.getD_some]
        exact recursive?_spec hb'
      have hu : u ∈ S := (hS u).mpr ⟨u, List.mem_singleton_self _, .inl rfl⟩
      have hmem : ∀ w, w ∈ S ↔ Reaches (Node.next shapes) u w := fun w => by
        rw [hS]; simp
      refine ⟨hrec u hu, ?_, ?_⟩
      · simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true']
        constructor
        · intro hf w hw
          have hw' := (hmem w).mpr hw
          obtain ⟨h1, h2⟩ := hf w hw'
          refine ⟨h1, fun ht => ?_⟩
          have := (hrec w hw').mpr ht
          simp [h2] at this
        · intro hf w hw
          have hw' := (hmem w).mp hw
          obtain ⟨h1, h2⟩ := hf w hw'
          refine ⟨h1, ?_⟩
          cases hr : (Fren.Core.recursive? shapes w).getD true
          · rfl
          · exact absurd ((hrec w hw).mp hr) h2
      · simp only [List.any_eq_true, Bool.or_eq_true]
        constructor
        · rintro ⟨w, hw, hg⟩
          exact ⟨w, (hmem w).mp hw, hg.imp id (hrec w hw).mp⟩
        · rintro ⟨w, hw, hg⟩
          have hw' := (hmem w).mpr hw
          exact ⟨w, hw', hg.imp id (hrec w hw').mpr⟩
    · simp at h

/-- When the facts of `t` are known, `t` is built from the nodes that
`builtOf` gives, which are closed. -/
theorem builtOf_spec {shapes : Lean.Name → Option DataShape} {t : Node} {F : Fren.Core.TypeFacts}
    (h : Fren.Core.typeFacts? shapes t = some F) :
    (∀ x, x ∈ builtOf shapes t ↔ Reaches (Node.next shapes) t x) ∧ Closed (Node.next shapes) (builtOf shapes t) := by
  simp only [Fren.Core.typeFacts?, Option.bind_eq_bind] at h
  cases hb : Fren.Core.reach (Node.next shapes) Fren.Core.reachFuel [t] [] with
  | none => simp [hb] at h
  | some S =>
    have := reach_eq _ hb
    simp only [builtOf, hb, Option.getD_some]
    exact ⟨fun x => by rw [this.1]; simp, this.2⟩

/-- The closure of the constituent relation over the nodes that `t` is
built from: from one of them, the closure of `Step`. -/
theorem transGen_constituents {shapes : Lean.Name → Option DataShape} {t : Node}
    (hc : Closed (Node.next shapes) (builtOf shapes t)) {a b : Node} :
    Relation.TransGen (fun x y => (x, y) ∈ constituentsOf shapes t) a b ↔
      a ∈ builtOf shapes t ∧ Relation.TransGen (Step (Node.next shapes)) a b := by
  have hsrc : ∀ {a b}, Relation.TransGen (fun x y => (x, y) ∈ constituentsOf shapes t) a b → a ∈ builtOf shapes t :=
    fun h => by
      induction h with
      | single h => exact (mem_edges _ |>.mp (FinSet.mem_ofList.mp h)).1
      | tail _ _ ih => exact ih
  have heq : (fun x y => (x, y) ∈ constituentsOf shapes t) = (fun x y => (x, y) ∈ edges (Node.next shapes) (builtOf shapes t)) := by
    funext x y; simp [constituentsOf]
  constructor
  · intro h
    have ha := hsrc h
    rw [heq] at h
    exact ⟨ha, (transGen_edges _ hc ha).mp h⟩
  · rintro ⟨ha, h⟩
    rw [heq]
    exact (transGen_edges _ hc ha).mpr h

/-- A node is finite by itself as `lang::own_finite?` says. -/
theorem own_finite_iff (n : Node) : lang.own_finite? (kindOf n.ty) n.bounded = true ↔ n.former.finite = true := by
  obtain ⟨t, b, es⟩ := n
  cases t <;> simp [Node.ty, Node.bounded, Fren.Core.Node.former, kindOf, lang.own_finite?, lang.former]

/-- A node's former is growing as `lang::former` says. -/
theorem growing_iff (n : Node) : (lang.former (kindOf n.ty)).growing? = true ↔ n.former.growing = true := by
  obtain ⟨t, b, es⟩ := n
  cases t <;> simp [Node.ty, Fren.Core.Node.former, kindOf, lang.former]

/-- The facts of a node `u` that `t` is built from, over the constituent
relation of `t`, are those that `typeFacts?` gives `u`. -/
theorem facts_at {shapes : Lean.Name → Option DataShape} {t u : Node} {F G : Fren.Core.TypeFacts}
    (hF : Fren.Core.typeFacts? shapes t = some F) (hu : u ∈ builtOf shapes t)
    (hG : Fren.Core.typeFacts? shapes u = some G) :
    let R := fun x y => (x, y) ∈ constituentsOf shapes t
    (G.recursive = true ↔ Relation.TransGen R u u) ∧
    (G.finite = true ↔ ∀ w, Relation.TransGen R u w ∨ w = u → w.former.finite = true ∧ ¬Relation.TransGen R w w) ∧
    (G.unbounded = true ↔ ∃ w, (Relation.TransGen R u w ∨ w = u) ∧
      (w.former.growing = true ∨ Relation.TransGen R w w)) := by
  intro R
  obtain ⟨hmem, hc⟩ := builtOf_spec hF
  obtain ⟨hr, hf, hb⟩ := typeFacts_spec hG
  have tg : ∀ {a b}, Relation.TransGen R a b ↔ a ∈ builtOf shapes t ∧ Relation.TransGen (Step (Node.next shapes)) a b :=
    transGen_constituents hc
  have inS : ∀ {w}, Reaches (Node.next shapes) u w → w ∈ builtOf shapes t := fun h => mem_of_closed _ hc hu h
  have reach : ∀ w, (Relation.TransGen R u w ∨ w = u) ↔ Reaches (Node.next shapes) u w := fun w => by
    rw [tg]
    constructor
    · rintro (⟨_, h⟩ | rfl)
      · exact .inr h
      · exact .inl rfl
    · rintro (rfl | h)
      · exact .inr rfl
      · exact .inl ⟨hu, h⟩
  have self : ∀ {w}, Reaches (Node.next shapes) u w →
      (Relation.TransGen R w w ↔ Relation.TransGen (Step (Node.next shapes)) w w) := fun h => by
    rw [tg]; exact ⟨And.right, fun h' => ⟨inS h, h'⟩⟩
  refine ⟨by rw [hr, tg]; exact ⟨fun h => ⟨hu, h⟩, And.right⟩, ?_, ?_⟩
  · rw [hf]
    constructor
    · intro h w hw
      have hw' := (reach w).mp hw
      rw [self hw']
      exact h w hw'
    · intro h w hw
      have := h w ((reach w).mpr hw)
      rwa [self hw] at this
  · rw [hb]
    constructor
    · rintro ⟨w, hw, hg⟩
      exact ⟨w, (reach w).mpr hw, by rwa [self hw]⟩
    · rintro ⟨w, hw, hg⟩
      have hw' := (reach w).mp hw
      exact ⟨w, hw', by rwa [self hw'] at hg⟩

/-- A record's former is not growing. -/
theorem growing_of_record (n : Node) (h : kindOf n.ty = .RecordTy) : n.former.growing = false := by
  obtain ⟨t, b, es⟩ := n
  cases t <;> simp_all [Node.ty, kindOf, Fren.Core.Node.former]

theorem typeFacts_eq {shapes : Lean.Name → Option DataShape} {t : Node} {F : Fren.Core.TypeFacts}
    (h : Fren.Core.typeFacts? shapes t = some F) : Fren.Core.typeFacts shapes t = F := by
  simp [Fren.Core.typeFacts, h]

theorem self_mem_builtOf {shapes : Lean.Name → Option DataShape} {t : Node} {F : Fren.Core.TypeFacts}
    (h : Fren.Core.typeFacts? shapes t = some F) : t ∈ builtOf shapes t :=
  ((builtOf_spec h).1 t).mpr (.inl rfl)

/-! ## The facts (`Reqs/Lang/Types#finite-types`) -/

-- For every type and declarations whose facts are known, over the
-- constituents that the declarations give: the facts that both front ends
-- compute.
impl type_facts: lang::type_facts for (shapes : Lean.Name → Option DataShape) (t : Node)
    (_known : (Fren.Core.typeFacts? shapes t).isSome) {
  ty := t,
  constituents := constituentsOf shapes t,
  recursive? := (Fren.Core.typeFacts shapes t).recursive,
  finite? := (Fren.Core.typeFacts shapes t).finite,
  unbounded? := (Fren.Core.typeFacts shapes t).unbounded,
} by
  intro shapes t h _
  obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp h
  have hof := own_finite_iff
  have hg := growing_iff
  simp only [fren_spec] at hof hg
  have ⟨hr, hf, hb⟩ := facts_at hF (self_mem_builtOf hF) hF
  simp only [fren_spec, FinSet.mem_union, FinSet.mem_image, FinSet.mem_singleton, exists_eq_left, FinSet.mem_closure,
    hof, hg, typeFacts_eq hF]
  exact ⟨hr, hf, hb⟩

/-! ## Quantifiers (`Reqs/Lang/Quantifiers#types`) -/

-- For every type and declarations whose facts are known, over the
-- constituents that the declarations give: whether a quantifier over it is
-- expanded, by the facts that both front ends compute (`binderValues`).
impl quantified_type: lang::quantified_type for (shapes : Lean.Name → Option DataShape) (t : Node)
    (_known : (Fren.Core.typeFacts? shapes t).isSome) {
  ty := t,
  constituents := constituentsOf shapes t,
  listed? := (Fren.Core.typeFacts shapes t).listed,
} by
  intro shapes t h _
  obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp h
  refine ⟨t, constituentsOf shapes t, F.recursive, F.finite, F.unbounded, ?_⟩
  have hof := own_finite_iff
  have hg := growing_iff
  simp only [fren_spec] at hof hg
  have ⟨hr, hf, hb⟩ := facts_at hF (self_mem_builtOf hF) hF
  simp only [fren_spec, FinSet.mem_union, FinSet.mem_image, FinSet.mem_singleton, exists_eq_left, FinSet.mem_closure,
    hof, hg, typeFacts_eq hF, Fren.Core.TypeFacts.listed, Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨by simp, ⟨trivial, trivial⟩, trivial, hr, hf, hb⟩

/-! ## Variables (`Reqs/Lang/Procedures#members`) -/

-- For every variable, and type and declarations whose facts are known:
-- the check that both front ends call, with the facts that both compute.
impl variable_type: lang::variable_type for (o d : Bool) (shapes : Lean.Name → Option DataShape) (t : Node)
    (_known : (Fren.Core.typeFacts? shapes t).isSome) {
  output? := o,
  ty := t,
  constituents := constituentsOf shapes t,
  defined? := d,
  accepted? := Fren.Core.variableTypeAccepted o (Fren.Core.typeFacts shapes t).unbounded d,
} by
  intro o d shapes t h _
  obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp h
  refine ⟨t, constituentsOf shapes t, F.recursive, F.finite, F.unbounded, ?_⟩
  have hof := own_finite_iff
  have hg := growing_iff
  simp only [fren_spec] at hof hg
  have ⟨hr, hf, hb⟩ := facts_at hF (self_mem_builtOf hF) hF
  simp only [fren_spec, FinSet.mem_union, FinSet.mem_image, FinSet.mem_singleton, exists_eq_left, FinSet.mem_closure,
    hof, hg, typeFacts_eq hF]
  refine ⟨by cases o <;> cases d <;> simp [Fren.Core.variableTypeAccepted], ⟨trivial, trivial⟩, trivial, hr, hf, hb⟩

/-! ## Newtypes (`Reqs/Lang/Items#newtypes`) -/

-- For every newtype and declarations whose facts are known, of the newtype
-- and of its underlying type: the checks that both front ends use, with
-- the facts of its underlying type that both compute.
impl newtype: lang::newtype for (n : Nat) (f : Bool) (shapes : Lean.Name → Option DataShape) (t u : Node)
    (_known : (Fren.Core.typeFacts? shapes t).isSome) (_underKnown : (Fren.Core.typeFacts? shapes u).isSome) {
  n_fields := n,
  field_accepted? := f,
  ty := t,
  underlying := u,
  constituents := constituentsOf shapes t,
  accepted? := Fren.Core.newtypeAccepted n f,
  unbounded? := Fren.Core.newtypeUnbounded (Fren.Core.typeFacts shapes u).unbounded,
} by
  intro n f shapes t u h hu' hs
  obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨G, hG⟩ := Option.isSome_iff_exists.mp hu'
  refine ⟨t, constituentsOf shapes t, F.recursive, F.finite, F.unbounded, ?_⟩
  have hof := own_finite_iff
  have hg := growing_iff
  simp only [fren_spec] at hof hg hs
  obtain ⟨hk, himg, hnr⟩ := hs
  have ht := self_mem_builtOf hF
  have hc : ∀ v, (t, v) ∈ constituentsOf shapes t ↔ v = u := fun v => by
    have := FinSet.ext_iff.mp himg v
    simpa using this
  have huS : u ∈ builtOf shapes t := by
    have := (hc u).mpr rfl
    exact (mem_edges _ |>.mp (FinSet.mem_ofList.mp this)) |> fun ⟨_, hb⟩ => by
      obtain ⟨l, hl, hv⟩ := (builtOf_spec hF).2 t ht
      rw [hl] at hb
      exact hv u hb
  have ⟨hr, hf, hb⟩ := facts_at hF ht hF
  have ⟨_, _, hbu⟩ := facts_at hF huS hG
  simp only [fren_spec, FinSet.mem_union, FinSet.mem_image, FinSet.mem_singleton, exists_eq_left, FinSet.mem_closure,
    hof, hg, typeFacts_eq hG]
  refine ⟨⟨by simp [Fren.Core.newtypeAccepted]; omega, ?_⟩, ⟨trivial, trivial⟩, trivial, hr, hf, hb⟩
  -- The newtype is a record and not recursive, so it is unbounded as its
  -- one constituent is.
  simp only [Fren.Core.newtypeUnbounded]
  rw [hbu, hb]
  have hnr' : ¬Relation.TransGen (fun x y => (x, y) ∈ constituentsOf shapes t) t t := by
    simpa [FinSet.mem_closure] using hnr
  have hgt : t.former.growing = false := growing_of_record t hk
  constructor
  · rintro ⟨w, hw, hgw⟩
    refine ⟨w, ?_, hgw⟩
    rcases hw with hw | rfl
    · exact .inl (Relation.TransGen.trans (.single ((hc u).mpr rfl)) hw)
    · exact .inl (.single ((hc w).mpr rfl))
  · rintro ⟨w, hw, hgw⟩
    rcases hw with hw | rfl
    · rcases transGen_iff_head.mp hw with ⟨v, hv, hw'⟩
      have := (hc v).mp hv
      subst this
      exact ⟨w, hw'.elim (fun e => .inr e) .inl, hgw⟩
    · rcases hgw with hgw | hgw
      · simp [hgt] at hgw
      · exact absurd hgw hnr'

/-! ## Operators of newtypes (`Reqs/Lang/Expressions#newtypes`) -/

/-- The pairs `(n, under(n))` of the newtypes of `t`'s chain: `t`, if it
is a newtype, and those of its underlying type (`lang::newtype_operator`). -/
def undersOf : Fren.Core.Ty → List (Fren.Core.Ty × Fren.Core.Ty)
  | .newtype p v => (.newtype p v, v) :: undersOf v
  | _ => []

/-- The base of `t`'s chain: the first type that is not a newtype. -/
def baseOf : Fren.Core.Ty → Fren.Core.Ty
  | .newtype _ v => baseOf v
  | t => t

theorem undersOf_source : ∀ {u a b : Fren.Core.Ty}, (a, b) ∈ undersOf u → ∃ p, a = .newtype p b
  | .newtype p v, a, b, h => by
    simp only [undersOf, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨p, rfl⟩
    · exact undersOf_source h
  | .bool, _, _, h | .int, _, _, h | .nat, _, _, h | .string, _, _, h | .set _, _, _, h | .rel .., _, _, h
  | .seq _, _, _, h | .enum .., _, _, h | .record .., _, _, h | .abstract _, _, _, h | .param .., _, _, h => by
    simp [undersOf] at h

/-- A type that is not a newtype is the one type built from it, over a
relation of newtypes and their underlying types. -/
theorem exists_base_leaf {R : FinSet (Fren.Core.Ty × Fren.Core.Ty)} (hR : ∀ a b, (a, b) ∈ R → ∃ p, a = .newtype p b)
    {N : Fren.Core.Ty → Bool} (hN : ∀ t, N t = true ↔ ∃ p v, t = .newtype p v) (P : Fren.Core.Ty → Prop)
    (w : Fren.Core.Ty) (hw : ∀ p v, w ≠ .newtype p v) :
    (∃ b, (b ∈ lang.chain Fren.Core.Ty w R ∧ ¬N b = true) ∧ P b) ↔ P w := by
  have := exists_chain (C := R) (t := w) (p := fun b => ¬N b = true ∧ P b)
  simp only [and_assoc] at this ⊢
  rw [this]
  constructor
  · rintro (⟨_, h⟩ | ⟨v, hv, _⟩)
    · exact h
    · obtain ⟨p, e⟩ := hR _ _ hv
      exact absurd e (hw p v)
  · intro h
    refine .inl ⟨fun hn => ?_, h⟩
    obtain ⟨p, v, e⟩ := (hN w).mp hn
    exact hw p v e

/-- Over a relation of newtypes and their underlying types that holds `w`'s
chain, a type with a property is built from `w` and not a newtype, by `N`,
exactly when `w`'s base has it. -/
theorem exists_base {R : FinSet (Fren.Core.Ty × Fren.Core.Ty)} (hR : ∀ a b, (a, b) ∈ R → ∃ p, a = .newtype p b)
    {N : Fren.Core.Ty → Bool} (hN : ∀ t, N t = true ↔ ∃ p v, t = .newtype p v) (P : Fren.Core.Ty → Prop) :
    ∀ w : Fren.Core.Ty, (∀ x ∈ undersOf w, x ∈ R) →
      ((∃ b, (b ∈ lang.chain Fren.Core.Ty w R ∧ ¬N b = true) ∧ P b) ↔ P (baseOf w))
  | .newtype p v, hw => by
    have hv : ∀ x, (Fren.Core.Ty.newtype p v, x) ∈ R ↔ x = v := fun x =>
      ⟨fun h => by obtain ⟨_, e⟩ := hR _ _ h; cases e; rfl,
       fun e => e ▸ hw _ (by simp [undersOf, e])⟩
    have := exists_chain (C := R) (t := .newtype p v) (p := fun b => ¬N b = true ∧ P b)
    simp only [and_assoc] at this ⊢
    rw [this]
    simp only [hv, exists_eq_left, baseOf, hN, not_exists]
    rw [← exists_base hR hN P v fun x hx => hw x (by simp [undersOf, hx])]
    simp [and_assoc, hN]
  | .bool, _ | .int, _ | .nat, _ | .string, _ | .set _, _ | .rel .., _ | .seq _, _ | .enum .., _ | .record .., _
  | .abstract _, _ | .param .., _ => exists_base_leaf hR hN P _ (by intro _ _ h; cases h)

theorem newtypeOpAccepted_add : ∀ (t : Fren.Core.Ty) (o : Bool),
    Fren.Core.newtypeOpAccepted .add t o = (baseOf t matches .int | .nat)
  | .newtype _ v, _ => by simp only [Fren.Core.newtypeOpAccepted, baseOf]; exact newtypeOpAccepted_add v false
  | .bool, _ | .int, _ | .nat, _ | .string, _ | .set _, _ | .rel .., _ | .seq _, _ | .enum .., _ | .record .., _
  | .abstract _, _ | .param .., _ => by simp [Fren.Core.newtypeOpAccepted, baseOf]

theorem newtypeOpAccepted_sub : ∀ (t : Fren.Core.Ty) (o : Bool),
    Fren.Core.newtypeOpAccepted .sub t o = (baseOf t matches .int)
  | .newtype _ v, _ => by simp only [Fren.Core.newtypeOpAccepted, baseOf]; exact newtypeOpAccepted_sub v false
  | .bool, _ | .int, _ | .nat, _ | .string, _ | .set _, _ | .rel .., _ | .seq _, _ | .enum .., _ | .record .., _
  | .abstract _, _ | .param .., _ => by simp [Fren.Core.newtypeOpAccepted, baseOf]

-- For every operator, underlying type and whether the newtype is ordered,
-- over the underlying types of its chain: the check that both front ends
-- use, which follows the chain to its base.
impl newtype_operator: lang::newtype_operator for (op : Fren.Core.NewtypeOp) (u : Fren.Core.Ty) (o : Bool) {
  op := toNewtypeOp op,
  underlying := u,
  ordered? := o,
  unders := FinSet.ofList (undersOf u),
  accepted? := Fren.Core.newtypeOpAccepted op u o,
} by
  intro op u o _
  have hR : ∀ a b, (a, b) ∈ FinSet.ofList (undersOf u) → ∃ p, a = .newtype p b :=
    fun _ _ h => undersOf_source (FinSet.mem_ofList.mp h)
  have hw : ∀ x ∈ undersOf u, x ∈ FinSet.ofList (undersOf u) := fun _ => FinSet.mem_ofList.mpr
  have hN : ∀ t, isNewtype t = true ↔ ∃ p v, t = .newtype p v := by
    intro t; cases t <;> simp [isNewtype]
  simp only [fren_spec]
  cases op <;> simp only [toNewtypeOp, Fren.Core.newtypeOpAccepted, newtypeOpAccepted_add, newtypeOpAccepted_sub,
    reduceCtorEq, ite_true, ite_false, decide_eq_true_eq]
  case add =>
    rw [exists_base hR hN (fun b => kindOf b ∈ ({lang.ValueType.IntTy, lang.ValueType.NatTy} : FinSet _)) u hw]
    cases baseOf u <;> simp [kindOf]
  case sub =>
    rw [exists_base hR hN (fun b => kindOf b = lang.ValueType.IntTy) u hw]
    cases baseOf u <;> simp [kindOf]
  all_goals rfl


/-! ## Well-founded enumerations (`Reqs/Lang/Items#enumerations`) -/

-- For every enumeration `t`, declarations, variants `vs` and their
-- payloads' types `pay`, over the constituents of every payload's type,
-- whose closure is known: the count that both front ends compare, of the
-- variants that `Fren.Core.recursiveVariant` finds recursive, as both
-- front ends count them.
impl well_founded: lang::well_founded for (shapes : Lean.Name → Option DataShape) (t : Node) (vs : List Lean.Name)
    (pay : Lean.Name → List Node)
    (_known : (Fren.Core.reach (Node.next shapes) Fren.Core.reachFuel (vs.flatMap pay) []).isSome)
    (_each : ∀ u ∈ vs.flatMap pay, (Fren.Core.reach (Node.next shapes) Fren.Core.reachFuel [u] []).isSome) {
  ty := t,
  constituents := FinSet.ofList (edges (Node.next shapes)
    ((Fren.Core.reach (Node.next shapes) Fren.Core.reachFuel (vs.flatMap pay) []).getD [])),
  variants := FinSet.ofList vs,
  payloads := FinSet.ofList (vs.flatMap fun v => (pay v).map (v, ·)),
  accepted? := Fren.Core.wellFounded vs.length (vs.filter fun v => Fren.Core.recursiveVariant shapes t (pay v)).length,
} by
  intro shapes t vs pay hj he _
  obtain ⟨S, hS⟩ := Option.isSome_iff_exists.mp hj
  obtain ⟨hmem, hc⟩ := reach_eq _ hS
  have hi : ∀ v u, (v, u) ∈ vs.flatMap (fun v => (pay v).map (v, ·)) ↔ v ∈ vs ∧ u ∈ pay v := by
    intro v u
    simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨w, hw, u', hu, rfl, rfl⟩
      exact ⟨hw, hu⟩
    · rintro ⟨hv, hu⟩
      exact ⟨v, hv, u, hu, rfl, rfl⟩
  -- A payload's type is recursive, as `recursiveVariant` finds it, exactly
  -- when the enumeration is built from it.
  have hrec : ∀ v ∈ vs, ∀ u ∈ pay v, ((u == t || (Fren.Core.reach (Node.next shapes) Fren.Core.reachFuel [u] []).all
      (·.contains t)) = true ↔ (Relation.TransGen (fun x y => (x, y) ∈ edges (Node.next shapes) S) u t ∨ t = u)) := by
    intro v hv u hu
    have huj : u ∈ vs.flatMap pay := List.mem_flatMap.mpr ⟨v, hv, hu⟩
    have huS : u ∈ S := (hmem u).mpr ⟨u, huj, .inl rfl⟩
    obtain ⟨R, hR⟩ := Option.isSome_iff_exists.mp (he u huj)
    have hRm := (reach_eq _ hR).1
    rw [transGen_edges _ hc huS]
    simp only [hR, Option.all_some, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, hRm, List.mem_singleton,
      exists_eq_left, Reaches]
    constructor
    · rintro (rfl | rfl | h)
      · exact .inr rfl
      · exact .inr rfl
      · exact .inl h
    · rintro (h | rfl)
      · exact .inr (.inr h)
      · exact .inl rfl
  simp only [hS, Option.getD_some, fren_spec, Fren.Core.wellFounded, decide_eq_true_eq,
    List.length_filter_lt_length_iff_exists, FinSet.mem_ofList, FinSet.mem_union, FinSet.mem_image,
    FinSet.mem_singleton, exists_eq_left, FinSet.mem_closure, Fren.Core.recursiveVariant, List.any_eq_true,
    not_exists, not_and]
  constructor
  · rintro ⟨v, hv, hr⟩
    refine ⟨v, hv, fun u hu hb => hr u ((hi v u).mp hu).2 ?_⟩
    exact (hrec v hv u ((hi v u).mp hu).2).mpr hb
  · rintro ⟨v, hv, hr⟩
    refine ⟨v, hv, fun u hu hb => hr u ((hi v u).mpr ⟨hv, hu⟩) ((hrec v hv u hu).mp hb)⟩

end Fren.Impls
