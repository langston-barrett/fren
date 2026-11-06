-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-! ## Merging the facts found on several paths (`lang::merged_facts`) -/

section MergeGuarded

variable {P : Type} (within : P → P → Bool)

/-- Neither of the paths `a` and `b` is within the other. -/
def Incomparable (a b : P) : Prop := within a b = false ∧ within b a = false

theorem mem_addPath {ps : List P} {p q : P} (h : q ∈ Fren.Core.addPath within ps p) : q ∈ ps ∨ q = p := by
  unfold Fren.Core.addPath at h
  split at h
  · exact .inl h
  · rcases List.mem_append.mp h with h | h
    · exact .inl (List.mem_filter.mp h).1
    · exact .inr (List.mem_singleton.mp h)

/-- Each of the paths `ps`, and the new one `p`, has one that `addPath`
keeps within it. -/
theorem addPath_covers (refl : ∀ a, within a a = true) (ps : List P) (p : P) :
    (∀ q ∈ ps, ∃ q' ∈ Fren.Core.addPath within ps p, within q' q = true) ∧
    ∃ q' ∈ Fren.Core.addPath within ps p, within q' p = true := by
  unfold Fren.Core.addPath
  split
  · next h =>
    obtain ⟨q, hq, hw⟩ := List.any_eq_true.mp h
    exact ⟨fun q hq => ⟨q, hq, refl q⟩, q, hq, hw⟩
  · refine ⟨fun q hq => ?_, p, List.mem_append_right _ (List.mem_singleton_self p), refl p⟩
    by_cases hw : within p q = true
    · exact ⟨p, List.mem_append_right _ (List.mem_singleton_self p), hw⟩
    · exact ⟨q, List.mem_append_left _ (List.mem_filter.mpr ⟨hq, by simpa using hw⟩), refl q⟩

theorem addPath_pairwise {ps : List P} (p : P) (h : ps.Pairwise (Incomparable within)) :
    (Fren.Core.addPath within ps p).Pairwise (Incomparable within) := by
  unfold Fren.Core.addPath
  split
  · exact h
  · next hn =>
    rw [List.pairwise_append]
    refine ⟨h.filter _, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    obtain ⟨ha, hf⟩ := List.mem_filter.mp ha
    simp only [List.any_eq_true, not_exists, not_and] at hn
    exact ⟨by simpa using hn a ha, by simpa using hf⟩

/-- Two distinct members of a list pairwise related by a symmetric `R` are
related. -/
theorem pairwise_mem {R : P → P → Prop} (hR : ∀ {a b}, R a b → R b a) :
    ∀ {l : List P}, l.Pairwise R → ∀ {a b}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · subst h1; exact h.1 b h2
    · subst h2; exact hR (h.1 a h1)
    · exact pairwise_mem hR h.2 h1 h2 hne

/-- Two positions of a list without duplicates that hold the same member
are the same. -/
theorem nodup_getElem_inj {α : Type} {l : List α} (h : l.Nodup) {i j : Nat} (hi : i < l.length)
    (hj : j < l.length) (e : l[i] = l[j]) : i = j := by
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact absurd e ((List.pairwise_iff_getElem.mp h) i j hi hj hlt)
  · exact heq
  · exact absurd e.symm ((List.pairwise_iff_getElem.mp h) j i hj hi hgt)

/-- What `mergeGuarded` keeps of the facts found so far, `pre`: each fact
once, with only paths on which it was found, among them one within each
such path, and none within another. -/
structure MergeInv {F : Type} (acc : List (F × List P)) (pre : List (F × P)) : Prop where
  nodup : (acc.map (·.1)).Nodup
  keys : ∀ f, f ∈ acc.map (·.1) ↔ f ∈ pre.map (·.1)
  sound : ∀ e ∈ acc, ∀ q ∈ e.2, (e.1, q) ∈ pre
  covers : ∀ x ∈ pre, ∃ e ∈ acc, e.1 = x.1 ∧ ∃ q ∈ e.2, within q x.2 = true
  antichain : ∀ e ∈ acc, e.2.Pairwise (Incomparable within)

theorem mergeStep_inv {F : Type} [BEq F] [LawfulBEq F] (refl : ∀ a, within a a = true)
    (trans : ∀ a b c, within a b = true → within b c = true → within a c = true)
    {acc : List (F × List P)} {pre : List (F × P)} (x : F × P) (h : MergeInv within acc pre) :
    MergeInv within (Fren.Core.mergeStep within acc x) (pre ++ [x]) := by
  unfold Fren.Core.mergeStep
  split
  · next hx =>
    obtain ⟨e0, he0, hk0⟩ := List.any_eq_true.mp hx
    have hk0 : e0.1 = x.1 := by simpa using hk0
    have hkeys : (acc.map fun e => (e.1, if e.1 == x.1 then Fren.Core.addPath within e.2 x.2 else e.2)).map (·.1)
        = acc.map (·.1) := by simp [Function.comp_def]
    refine ⟨hkeys ▸ h.nodup, fun f => ?_, fun e' he' q hq => ?_, fun y hy => ?_, fun e' he' => ?_⟩
    · rw [hkeys, h.keys f]
      simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton]
      constructor
      · exact .inl
      · rintro (h' | rfl)
        · exact h'
        · exact (h.keys _).mp (List.mem_map.mpr ⟨e0, he0, hk0⟩)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      dsimp only at hq ⊢
      split at hq
      · next hex =>
        have hex : e.1 = x.1 := by simpa using hex
        rcases mem_addPath within hq with hq | rfl
        · exact List.mem_append_left _ (h.sound e he q hq)
        · exact List.mem_append_right _ (by rw [hex]; simp)
      · exact List.mem_append_left _ (h.sound e he q hq)
    · rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨e, he, hk, q, hq, hw⟩ := h.covers y hy
        refine ⟨_, List.mem_map_of_mem he, hk, ?_⟩
        dsimp only
        split
        · obtain ⟨q', hq', hw'⟩ := (addPath_covers within refl e.2 x.2).1 q hq
          exact ⟨q', hq', trans _ _ _ hw' hw⟩
        · exact ⟨q, hq, hw⟩
      · rw [List.mem_singleton] at hy
        subst hy
        refine ⟨_, List.mem_map_of_mem he0, hk0, ?_⟩
        dsimp only
        rw [if_pos (by simpa using hk0)]
        exact (addPath_covers within refl e0.2 y.2).2
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      dsimp only
      split
      · exact addPath_pairwise within _ (h.antichain e he)
      · exact h.antichain e he
  · next hx =>
    have hx : x.1 ∉ acc.map (·.1) := by
      intro hm
      obtain ⟨e, he, hk⟩ := List.mem_map.mp hm
      exact hx (List.any_eq_true.mpr ⟨e, he, by simpa using hk⟩)
    refine ⟨?_, fun f => ?_, fun e he q hq => ?_, fun y hy => ?_, fun e he => ?_⟩
    · rw [List.map_append, List.nodup_append]
      refine ⟨h.nodup, by simp, fun a ha b hb => ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      exact fun e => hx (e ▸ ha)
    · simp only [List.map_append, List.mem_append, h.keys f]
      simp
    · rcases List.mem_append.mp he with he | he
      · exact List.mem_append_left _ (h.sound e he q hq)
      · rw [List.mem_singleton] at he
        subst he
        rw [List.mem_singleton.mp hq]
        exact List.mem_append_right _ (List.mem_singleton_self _)
    · rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨e, he, hk, q, hq, hw⟩ := h.covers y hy
        exact ⟨e, List.mem_append_left _ he, hk, q, hq, hw⟩
      · rw [List.mem_singleton] at hy
        subst hy
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, y.2, List.mem_singleton_self _, refl _⟩
    · rcases List.mem_append.mp he with he | he
      · exact h.antichain e he
      · rw [List.mem_singleton] at he
        subst he
        exact List.pairwise_singleton _ _

theorem mergeGuarded_inv {F : Type} [BEq F] [LawfulBEq F] (refl : ∀ a, within a a = true)
    (trans : ∀ a b c, within a b = true → within b c = true → within a c = true) (found : List (F × P)) :
    MergeInv within (Fren.Core.mergeGuarded within found) found := by
  suffices ∀ (rest pre : List (F × P)) (acc : List (F × List P)), MergeInv within acc pre →
      MergeInv within (rest.foldl (Fren.Core.mergeStep within) acc) (pre ++ rest) by
    unfold Fren.Core.mergeGuarded
    simpa using this found [] [] ⟨List.nodup_nil, by simp, by simp, by simp, by simp⟩
  intro rest
  induction rest with
  | nil => intro pre acc h; simpa using h
  | cons x rest ih =>
    intro pre acc h
    simpa using ih (pre ++ [x]) _ (mergeStep_inv within refl trans x h)

/-- The merged facts are equivalent to those found (`lang::merged_facts`'s
first two conjuncts): wherever `holds` holds of the paths whose guards
hold, which it does of a path within one it holds of, the query asserts a
fact under paths one of which holds just when it was found on such a path. -/
theorem mergeGuarded_equivalent {F : Type} [BEq F] [LawfulBEq F] (refl : ∀ a, within a a = true)
    (trans : ∀ a b c, within a b = true → within b c = true → within a c = true) (found : List (F × P))
    (holds : P → Prop) (mono : ∀ q p, within q p = true → holds p → holds q) (f : F) :
    (∃ p, (f, p) ∈ found ∧ holds p) ↔
      ∃ e ∈ Fren.Core.mergeGuarded within found, e.1 = f ∧ ∃ q ∈ e.2, holds q := by
  have inv := mergeGuarded_inv within refl trans found
  constructor
  · rintro ⟨p, hp, hh⟩
    obtain ⟨e, he, hk, q, hq, hw⟩ := inv.covers (f, p) hp
    exact ⟨e, he, hk, q, hq, mono q p hw hh⟩
  · rintro ⟨e, he, rfl, q, hq, hh⟩
    exact ⟨q, inv.sound e he q hq, hh⟩

/-- Each fact that `mergeGuarded` keeps has a path, so `guardedFact` never
gets an empty list. -/
theorem mergeGuarded_nonempty {F : Type} [BEq F] [LawfulBEq F] (refl : ∀ a, within a a = true)
    (trans : ∀ a b c, within a b = true → within b c = true → within a c = true) (found : List (F × P)) :
    ∀ e ∈ Fren.Core.mergeGuarded within found, e.2 ≠ [] := by
  have inv := mergeGuarded_inv within refl trans found
  intro e he
  obtain ⟨x, hx, hk⟩ := List.mem_map.mp ((inv.keys e.1).mp (List.mem_map_of_mem he))
  obtain ⟨e', he', hk', q, hq, -⟩ := inv.covers x hx
  have : e' = e := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he'
    have := nodup_getElem_inj inv.nodup (by simpa using hj) (by simpa using hi) (by simpa using hk'.trans hk)
    subst this
    rfl
  subst this
  exact List.ne_nil_of_mem hq

end MergeGuarded

/-- The formula that `guardedFact` asserts for the paths that
`mergeGuarded` keeps: wherever `implies` means implication from all of
its guards and `disj` the disjunction of its paths' guards, as each front
end's do, it holds just when the fact does wherever all of some path's
guards hold. With `mergeGuarded_equivalent` and `mergeGuarded_nonempty`,
the query's formula for a fact is then equivalent to the fact under every
path on which it was found. That each front end's `implies` and `disj`
mean that is not proved: they build Lean terms and SMT-LIB text. -/
theorem guardedFact_holds {F G : Type} (implies : Array G → F → F) (disj : List (Array G) → G)
    (sat : F → Prop) (guard : G → Prop)
    (himp : ∀ gs f, sat (implies gs f) ↔ ((∀ g ∈ gs, guard g) → sat f))
    (hdisj : ∀ ps, guard (disj ps) ↔ ∃ p ∈ ps, ∀ g ∈ p, guard g)
    (f : F) (ps : List (Array G)) (hne : ps ≠ []) :
    sat (Fren.Core.guardedFact implies disj f ps) ↔ ((∃ p ∈ ps, ∀ g ∈ p, guard g) → sat f) := by
  match ps, hne with
  | [g], _ => simp [Fren.Core.guardedFact, himp]
  | p :: q :: rest, _ => simp [Fren.Core.guardedFact, himp, hdisj]

/-- The front ends' `within`, `guardsWithin`, is the inclusion of guards that
`pathWithin` decides of paths by position: so it is reflexive and
transitive, as `mergeGuarded_inv` needs. -/
theorem guardsWithin_iff {G : Type} [BEq G] [LawfulBEq G] (g h : Array G) :
    Fren.Core.guardsWithin g h = true ↔ ∀ x ∈ g, x ∈ h := by
  unfold Fren.Core.guardsWithin
  constructor
  · intro hall x hx
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
    simpa using Array.all_eq_true.mp hall i hi
  · intro hin
    exact Array.all_eq_true.mpr fun i hi => by simpa using hin _ (Array.getElem_mem hi)

/-- `mergeGuarded` at the front ends' own instantiation, paths given by
their guards and `guardsWithin` (`recursiveQueryFacts`): each fact once,
with only paths on which it was found, among them one within each such
path, and none within another, as `impl merged_facts` proves of paths by
position. -/
theorem mergeGuarded_guards {F G : Type} [BEq F] [LawfulBEq F] [BEq G] [LawfulBEq G]
    (found : List (F × Array G)) :
    MergeInv Fren.Core.guardsWithin (Fren.Core.mergeGuarded Fren.Core.guardsWithin found) found :=
  mergeGuarded_inv _ (fun a => (guardsWithin_iff a a).mpr fun _ h => h)
    (fun a b c hab hbc => (guardsWithin_iff a c).mpr fun x h =>
      (guardsWithin_iff b c).mp hbc x ((guardsWithin_iff a b).mp hab x h)) found

/-- The guards of the path `p`, of the pairs `guards` of each path and one
of its guards. -/
def guardsOfPath (guards : List (Nat × Nat)) (p : Nat) : List Nat := (guards.filter (·.1 == p)).map (·.2)

/-- Whether the path `p`'s guards are among `q`'s, as `guardsWithin`
decides it of their guards. -/
def pathWithin (guards : List (Nat × Nat)) (p q : Nat) : Bool := (guardsOfPath guards p).all (guardsOfPath guards q).contains

theorem pathWithin_iff (guards : List (Nat × Nat)) (p q : Nat) :
    pathWithin guards p q = true ↔ ∀ g, (p, g) ∈ guards → (q, g) ∈ guards := by
  simp only [pathWithin, guardsOfPath, List.all_eq_true, List.contains_iff_mem, List.mem_map, List.mem_filter,
    beq_iff_eq]
  constructor
  · intro h g hg
    obtain ⟨y, ⟨hy, hy1⟩, hy2⟩ := h g ⟨(p, g), ⟨hg, rfl⟩, rfl⟩
    have : y = (q, g) := Prod.ext hy1 hy2
    exact this ▸ hy
  · rintro h _ ⟨y, ⟨hy, rfl⟩, rfl⟩
    exact ⟨(q, y.2), ⟨h y.2 hy, rfl⟩, rfl⟩

/-- The guards of the path `p`, as the Req's `guards.image({p})`. -/
theorem mem_image_guards (guards : List (Nat × Nat)) (p : Nat) (x : Int) :
    x ∈ Fren.FinSet.image (Fren.FinSet.ofList (guards.map fun (g : Nat × Nat) => ((g.1 : Int), (g.2 : Int))))
      {(p : Int)} ↔ ∃ g : Nat, (p, g) ∈ guards ∧ (g : Int) = x := by
  simp only [Fren.FinSet.mem_image, Fren.FinSet.mem_singleton, Fren.FinSet.mem_ofList, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨_, rfl, ⟨a, b⟩, hab, ha, rfl⟩
    exact ⟨b, (Int.ofNat_inj.mp ha) ▸ hab, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, rfl, (p, g), hg, rfl, rfl⟩

theorem image_guards_subset (guards : List (Nat × Nat)) (p q : Nat) :
    Fren.FinSet.image (Fren.FinSet.ofList (guards.map fun (g : Nat × Nat) => ((g.1 : Int), (g.2 : Int)))) {(q : Int)} ⊆
      Fren.FinSet.image (Fren.FinSet.ofList (guards.map fun (g : Nat × Nat) => ((g.1 : Int), (g.2 : Int)))) {(p : Int)}
      ↔ pathWithin guards q p = true := by
  rw [Fren.FinSet.subset_def, pathWithin_iff]
  constructor
  · intro h g hg
    obtain ⟨g', hg', he⟩ := (mem_image_guards guards p _).mp (h _ ((mem_image_guards guards q _).mpr ⟨g, hg, rfl⟩))
    exact (Int.ofNat_inj.mp he) ▸ hg'
  · intro h x hx
    obtain ⟨g, hg, rfl⟩ := (mem_image_guards guards q x).mp hx
    exact (mem_image_guards guards p _).mpr ⟨g, h g hg, rfl⟩

-- Both front ends assert the facts of a query's recursive applications as
-- `mergeGuarded` merges them, from the paths on which their queue finds
-- them, given by their guards, of which `guardsWithin` is `pathWithin`:
-- over any facts found on any paths, with any guards.
impl merged_facts: lang::merged_facts for (found guards : List (Nat × Nat)) {
  found := Fren.FinSet.ofList (found.map fun (x : Nat × Nat) => ((x.1 : Int), (x.2 : Int))),
  guards := Fren.FinSet.ofList (guards.map fun (g : Nat × Nat) => ((g.1 : Int), (g.2 : Int))),
  asserted := Fren.FinSet.ofList ((Fren.Core.mergeGuarded (pathWithin guards) found).flatMap fun e =>
    e.2.map fun (q : Nat) => ((e.1 : Int), (q : Int))),
  assertions := Fren.FinSet.ofList ((Fren.Core.mergeGuarded (pathWithin guards) found).zipIdx.map
    fun (e : (Nat × List Nat) × Nat) => ((e.2 : Int), (e.1.1 : Int))),
  «merged?» := true,
} by
  intro found guards _
  have refl : ∀ a, pathWithin guards a a = true := fun a => (pathWithin_iff guards a a).mpr fun _ h => h
  have trans : ∀ a b c, pathWithin guards a b = true → pathWithin guards b c = true → pathWithin guards a c = true :=
    fun a b c hab hbc => (pathWithin_iff guards a c).mpr fun g h =>
      (pathWithin_iff guards b c).mp hbc g ((pathWithin_iff guards a b).mp hab g h)
  have inv := mergeGuarded_inv (pathWithin guards) refl trans found
  generalize Fren.Core.mergeGuarded (pathWithin guards) found = r at inv
  -- An entry of `r` by its fact.
  have entry : ∀ e ∈ r, ∀ e' ∈ r, e.1 = e'.1 → e = e' := by
    intro e he e' he' hk
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he'
    have := nodup_getElem_inj inv.nodup (by simpa using hi) (by simpa using hj) (by simpa using hk)
    subst this
    rfl
  unfold lang.merged_facts.ensures lang.merged_facts.ensure.rule
  refine ⟨fun _ => ⟨⟨⟨⟨?sound, ?covers⟩, ?antichain⟩, ?once⟩, ?facts⟩, fun _ => rfl⟩
  case sound =>
    rw [Fren.FinSet.subset_def]
    intro x hx
    simp only [Fren.FinSet.mem_ofList, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨e, he, q, hq, rfl⟩ := hx
    exact Fren.FinSet.mem_ofList.mpr (List.mem_map.mpr ⟨(e.1, q), inv.sound e he q hq, rfl⟩)
  case covers =>
    intro f p hfp
    simp only [Fren.FinSet.mem_ofList, List.mem_map, Prod.mk.injEq] at hfp
    obtain ⟨x, hx, rfl, rfl⟩ := hfp
    obtain ⟨e, he, hk, q, hq, hw⟩ := inv.covers x hx
    refine ⟨q, Fren.FinSet.mem_ofList.mpr (List.mem_flatMap.mpr ⟨e, he, List.mem_map.mpr ⟨q, hq, by rw [hk]⟩⟩), ?_⟩
    exact (image_guards_subset guards x.2 q).mpr hw
  case antichain =>
    rintro f p q ⟨⟨hp, hq⟩, hne⟩ hsub
    simp only [Fren.FinSet.mem_ofList, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hp hq
    obtain ⟨e, he, p', hp', rfl, rfl⟩ := hp
    obtain ⟨e', he', q', hq', hk, rfl⟩ := hq
    have := entry e he e' he' (Int.ofNat_inj.mp hk).symm
    subst this
    have hne : p' ≠ q' := fun h => hne (h ▸ rfl)
    have hw := (image_guards_subset guards p' q').mp hsub
    have h := pairwise_mem (fun {a b} (h : Incomparable (pathWithin guards) a b) => ⟨h.2, h.1⟩)
      (inv.antichain e he) hp' hq' hne
    exact absurd hw (by simp [h.2])
  case once =>
    rintro a b f ⟨ha, hb⟩
    simp only [Fren.FinSet.mem_ofList, List.mem_map, Prod.mk.injEq] at ha hb
    obtain ⟨⟨e, i⟩, hi, rfl, rfl⟩ := ha
    obtain ⟨⟨e', j⟩, hj, rfl, hk⟩ := hb
    rw [List.mem_zipIdx_iff_getElem?] at hi hj
    obtain ⟨hi1, hi2⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj1, hj2⟩ := List.getElem?_eq_some_iff.mp hj
    have hk' : e'.1 = e.1 := Int.ofNat_inj.mp (by simpa using hk)
    have : i = j := nodup_getElem_inj inv.nodup (by simpa using hi1) (by simpa using hj1)
      (by simp [hi2, hj2, hk'])
    rw [this]
  case facts =>
    apply Fren.FinSet.ext
    intro f
    simp only [Fren.FinSet.mem_range, Fren.FinSet.mem_domain, Fren.FinSet.mem_ofList, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨_, ⟨⟨e, i⟩, hi, rfl, rfl⟩⟩
      rw [List.mem_zipIdx_iff_getElem?] at hi
      obtain ⟨x, hx, hxk⟩ := List.mem_map.mp ((inv.keys e.1).mp (List.mem_map_of_mem (List.mem_of_getElem? hi)))
      exact ⟨x.2, x, hx, by simp [hxk], rfl⟩
    · rintro ⟨_, x, hx, rfl, rfl⟩
      obtain ⟨e, he, hk⟩ := List.mem_map.mp ((inv.keys x.1).mpr (List.mem_map_of_mem hx))
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      exact ⟨i, (r[i], i), List.mem_zipIdx_iff_getElem?.mpr (by simp), rfl, by rw [hk]⟩

end Fren.Impls
