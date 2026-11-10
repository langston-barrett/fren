import Fren.Impl
import Fren.Literate
import Fren.Trace
import Spec.Language.NamesAndScope

/-!
# Derivation tables and inductive derivations

A chapter that states a judgment in Fren writes a derivation as a *table*:
a snoc-list of rows in postorder, each row a one-layer form whose children
are positions of earlier rows, together with the row's conclusion. Fren has
no nested recursive types, so it cannot state the tree that a table stands
for. This module states it once, for any one-layer functor `F` and any
one-layer rule `R`, and proves that the two readings agree:

* `Valid.derives`: every row of a valid table unfolds to a term that has an
  inductive derivation of the row's conclusion;
* `Derives.table`: every inductive derivation has a valid table whose last
  row has its conclusion and unfolds to its term;
* `Unfolds.alike`, `Unfolds.unique`: rows that a bisimulation pairs unfold
  to the same term, so a row unfolds to one term;
* `Derives.unique`: a rule that determines its conclusion from the moded
  part of it determines the conclusion of every derivation;
* `Unfolds.mapped`: a table whose layers are rewritten row by row, as by a
  shift, unfolds to the term rewritten node by node (`Mapped`).

A chapter instantiates `Layer` for its functor, gives a `View` of its rows
and shows that its table check is `Valid`.
-/

open Fren.Lang
open spec.surface spec.names

namespace Spec.Tables

/-- A one-layer functor: a finitely branching container. `zip` says that it
preserves weak pullbacks, which every such container does. -/
class Layer (F : Type → Type) where
  map : {α β : Type} → (α → β) → F α → F β
  children : {α : Type} → F α → List α
  map_id : ∀ {α : Type} (l : F α), map (fun x => x) l = l
  map_map : ∀ {α β γ : Type} (f : α → β) (g : β → γ) (l : F α),
    map g (map f l) = map (fun x => g (f x)) l
  children_map : ∀ {α β : Type} (f : α → β) (l : F α),
    children (map f l) = (children l).map f
  map_congr : ∀ {α β : Type} (f g : α → β) (l : F α),
    (∀ c ∈ children l, f c = g c) → map f l = map g l
  zip : ∀ {α β γ : Type} (f : α → γ) (g : β → γ) (l : F α) (m : F β),
    map f l = map g m →
    ∃ z : F (α × β), map Prod.fst z = l ∧ map Prod.snd z = m ∧ ∀ c ∈ children z, f c.1 = g c.2

open Layer

/-- How a chapter's rows are read: a row's form, whose children are
positions, and its conclusion. -/
structure View (ρ : Type) (F : Type → Type) (J : Type) where
  form : ρ → F Int
  concl : ρ → J

section
variable {F : Type → Type} [Layer F] {ρ ρ' J J' K T : Type} [Inhabited ρ] [Inhabited ρ']

theorem mem_map_of_mem {α β : Type} (f : α → β) {l : F α} {c : α} (h : c ∈ children l) :
    f c ∈ children (map f l) := by
  rw [children_map]; exact List.mem_map.2 ⟨c, h, rfl⟩

theorem lookup_extend (earlier : Snoc ρ) (x : ρ) (p : Int) :
    lookup ρ (Snoc.Extend earlier x) p
      = if p = length ρ earlier then some x else lookup ρ earlier p := by
  simp only [lookup]

theorem lookup_earlier (earlier : Snoc ρ) (x : ρ) (p : Int) (h : p < length ρ earlier) :
    lookup ρ (Snoc.Extend earlier x) p = lookup ρ earlier p := by
  rw [lookup_extend, if_neg (by omega)]

theorem lookup_lt {rows : Snoc ρ} {p : Int} {r : ρ} (h : lookup ρ rows p = some r) :
    p < length ρ rows :=
  (Spec.Language.NamesAndScope.lookup_bound rows p r h).2

/-- `rows'` keeps every row of `rows` at its position. -/
def Extends (rows' rows : Snoc ρ) : Prop :=
  ∀ p r, lookup ρ rows p = some r → lookup ρ rows' p = some r

theorem Extends.refl (rows : Snoc ρ) : Extends rows rows := fun _ _ h => h

theorem Extends.trans {a b c : Snoc ρ} (h : Extends a b) (h' : Extends b c) : Extends a c :=
  fun p r hl => h p r (h' p r hl)

theorem Extends.extend (rows : Snoc ρ) (x : ρ) : Extends (Snoc.Extend rows x) rows := by
  intro p r h
  rw [lookup_earlier _ _ _ (lookup_lt h)]; exact h

/-- Row `r` at position `p` is an instance of the rule: its form's children
are earlier rows, and `R` relates their conclusions to the row's. -/
def Justified (V : View ρ F J) (R : F J → J → Prop) (rows : Snoc ρ) (p : Int) (r : ρ) : Prop :=
  ∃ a : F (Int × J), map Prod.fst a = V.form r ∧ R (map Prod.snd a) (V.concl r) ∧
    ∀ c ∈ children a, c.1 < p ∧ ∃ r', lookup ρ rows c.1 = some r' ∧ V.concl r' = c.2

/-- A table is valid when every row is justified. -/
def Valid (V : View ρ F J) (R : F J → J → Prop) (rows : Snoc ρ) : Prop :=
  ∀ p r, lookup ρ rows p = some r → Justified V R rows p r

theorem Valid.empty (V : View ρ F J) (R : F J → J → Prop) : Valid V R Snoc.Empty := by
  intro p r h; simp [lookup] at h

theorem Justified.mono {V : View ρ F J} {R : F J → J → Prop} {rows rows' : Snoc ρ} {p : Int}
    {r : ρ} (he : Extends rows' rows) (h : Justified V R rows p r) : Justified V R rows' p r := by
  obtain ⟨a, hf, hr, hc⟩ := h
  refine ⟨a, hf, hr, fun c hcm => ?_⟩
  obtain ⟨hlt, r', hl, hcl⟩ := hc c hcm
  exact ⟨hlt, r', he _ _ hl, hcl⟩

theorem Justified.restrict {V : View ρ F J} {R : F J → J → Prop} {earlier : Snoc ρ} {x : ρ}
    {p : Int} {r : ρ} (hp : p ≤ length ρ earlier)
    (h : Justified V R (Snoc.Extend earlier x) p r) : Justified V R earlier p r := by
  obtain ⟨a, hf, hr, hc⟩ := h
  refine ⟨a, hf, hr, fun c hcm => ?_⟩
  obtain ⟨hlt, r', hl, hcl⟩ := hc c hcm
  rw [lookup_earlier _ _ _ (by omega)] at hl
  exact ⟨hlt, r', hl, hcl⟩

/-- Validity row by row: the form in which a chapter's table check states it. -/
theorem valid_extend (V : View ρ F J) (R : F J → J → Prop) (earlier : Snoc ρ) (x : ρ) :
    Valid V R (Snoc.Extend earlier x)
      ↔ Valid V R earlier ∧ Justified V R earlier (length ρ earlier) x := by
  constructor
  · intro h
    refine ⟨fun p r hl => ?_, ?_⟩
    · have hlt := lookup_lt hl
      refine Justified.restrict (Int.le_of_lt hlt) (h p r ?_)
      rw [lookup_earlier _ _ _ hlt]; exact hl
    · refine Justified.restrict (Int.le_refl _) (h _ x ?_)
      rw [lookup_extend, if_pos rfl]
  · intro ⟨hv, hj⟩ p r hl
    rw [lookup_extend] at hl
    split at hl
    · next hp =>
      cases hl; subst hp
      exact hj.mono (Extends.extend earlier x)
    · exact (hv p r hl).mono (Extends.extend earlier x)

theorem Valid.mono {V : View ρ F J} {R R' : F J → J → Prop} {rows : Snoc ρ}
    (hr : ∀ l j, R l j → R' l j) (h : Valid V R rows) : Valid V R' rows := by
  intro p r hl
  obtain ⟨a, hf, hra, hc⟩ := h p r hl
  exact ⟨a, hf, hr _ _ hra, hc⟩

/-- Every row of a table valid for `R` and an invariant satisfies the invariant. -/
theorem Valid.invariant {V : View ρ F J} {R : F J → J → Prop} {Q : J → Prop} {rows : Snoc ρ}
    (h : Valid V (fun l j => R l j ∧ Q j) rows) {p : Int} {r : ρ}
    (hl : lookup ρ rows p = some r) : Q (V.concl r) := by
  obtain ⟨_, _, hra, _⟩ := h p r hl
  exact hra.2

/-- The row at position `p` unfolds to the term `t`: `t`'s outer layer is the
row's form, and each child of the form unfolds to the matching subterm. -/
inductive Unfolds (V : View ρ F J) (con : F T → T) (rows : Snoc ρ) : Int → T → Prop
  | node (p : Int) (r : ρ) (a : F (Int × T)) :
      lookup ρ rows p = some r → map Prod.fst a = V.form r →
      (∀ c ∈ children a, Unfolds V con rows c.1 c.2) →
      Unfolds V con rows p (con (map Prod.snd a))

/-- The inductive reading of a one-layer rule: a finite tree of instances
of `R` concludes `j` for the term `t`. -/
inductive Derives (con : F T → T) (R : F J → J → Prop) : T → J → Prop
  | node (a : F (T × J)) (j : J) :
      (∀ c ∈ children a, Derives con R c.1 c.2) → R (map Prod.snd a) j →
      Derives con R (con (map Prod.fst a)) j

theorem Unfolds.mono {V : View ρ F J} {con : F T → T} {rows rows' : Snoc ρ} {p : Int} {t : T}
    (he : Extends rows' rows) (h : Unfolds V con rows p t) : Unfolds V con rows' p t := by
  induction h with
  | node p r a hl hf _ ih => exact Unfolds.node p r a (he _ _ hl) hf ih

/-- Two positions are bisimilar under `P` when the forms of paired rows
have the same shape and payloads and their corresponding children are
paired again. -/
def Bisim (V : View ρ F J) (V' : View ρ' F J') (left : Snoc ρ) (right : Snoc ρ')
    (P : Int → Int → Prop) : Prop :=
  ∀ p q r r', P p q → lookup ρ left p = some r → lookup ρ' right q = some r' →
    ∃ z : F (Int × Int), map Prod.fst z = V.form r ∧ map Prod.snd z = V'.form r' ∧
      ∀ c ∈ children z, P c.1 c.2

/-- Paired rows unfold to the same term. -/
theorem Unfolds.alike {V : View ρ F J} {V' : View ρ' F J'} {con : F T → T} {left : Snoc ρ}
    {right : Snoc ρ'} {P : Int → Int → Prop} (hb : Bisim V V' left right P) {p : Int} {t : T}
    (h : Unfolds V con left p t) :
    ∀ q t', P p q → Unfolds V' con right q t' → t = t' := by
  induction h with
  | node p r a hl hf _ ih =>
    intro q t' hp h'
    cases h' with
    | node _ r' a' hl' hf' hc' =>
      obtain ⟨z, hz1, hz2, hz⟩ := hb p q r r' hp hl hl'
      obtain ⟨w1, hw1a, hw1z, hw1⟩ := zip Prod.fst Prod.fst a z (hf.trans hz1.symm)
      obtain ⟨w2, hw2w, hw2a, hw2⟩ :=
        zip (fun c : (Int × T) × (Int × Int) => c.2.2) Prod.fst w1 a' (by
          rw [hf', ← hz2, ← hw1z, map_map])
      have e1 : map Prod.snd a = map (fun c : ((Int × T) × (Int × Int)) × (Int × T) => c.1.1.2) w2 := by
        rw [← hw1a, ← hw2w, map_map, map_map]
      have e2 : map Prod.snd a' = map (fun c : ((Int × T) × (Int × Int)) × (Int × T) => c.2.2) w2 := by
        rw [← hw2a, map_map]
      rw [e1, e2]
      congr 1
      apply Layer.map_congr
      intro c hc
      have hcw : c.1 ∈ children w1 := by rw [← hw2w]; exact mem_map_of_mem _ hc
      have hca : c.1.1 ∈ children a := by rw [← hw1a]; exact mem_map_of_mem _ hcw
      have hcz : c.1.2 ∈ children z := by rw [← hw1z]; exact mem_map_of_mem _ hcw
      have hca' : c.2 ∈ children a' := by rw [← hw2a]; exact mem_map_of_mem _ hc
      refine ih c.1.1 hca c.2.1 c.2.2 ?_ (hc' c.2 hca')
      have h1 : c.1.1.1 = c.1.2.1 := hw1 c.1 hcw
      have h2 : c.1.2.2 = c.2.1 := hw2 c hc
      rw [h1, ← h2]; exact hz c.1.2 hcz

/-- A row unfolds to at most one term. -/
theorem Unfolds.unique {V : View ρ F J} {con : F T → T} {rows : Snoc ρ} {p : Int} {t t' : T}
    (h : Unfolds V con rows p t) (h' : Unfolds V con rows p t') : t = t' := by
  refine Unfolds.alike (P := fun p q => p = q) ?_ h p t' rfl h'
  intro p q r r' hpq hl hl'
  subst hpq
  rw [hl] at hl'; cases hl'
  refine ⟨map (fun i => (i, i)) (V.form r), ?_, ?_, ?_⟩
  · rw [map_map]; exact map_id _
  · rw [map_map]; exact map_id _
  · intro c hc
    rw [children_map] at hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
    rfl

theorem Derives.mono {con : F T → T} {R R' : F J → J → Prop} {t : T} {j : J}
    (hr : ∀ l j, R l j → R' l j) (h : Derives con R t j) : Derives con R' t j := by
  induction h with
  | node a j _ hra ih => exact Derives.node a j ih (hr _ _ hra)

/-- An invariant that the rule passes from a conclusion to its premises
holds at every node of a derivation whose conclusion satisfies it. -/
theorem Derives.strengthen {con : F T → T} {R : F J → J → Prop} (Q : J → Prop)
    (step : ∀ l j, R l j → Q j → ∀ c ∈ children l, Q c) {t : T} {j : J}
    (h : Derives con R t j) : Q j → Derives con (fun l j => R l j ∧ Q j) t j := by
  induction h with
  | node a j _ hra ih =>
    intro hq
    exact Derives.node a j
      (fun c hc => ih c hc (step _ j hra hq c.2 (mem_map_of_mem _ hc))) ⟨hra, hq⟩

/-- Derivations of one term agree. `key` is the moded part of a conclusion,
which the context of use fixes; `det` says that the rule determines a
conclusion from its key, given that each premise is determined by its key. -/
theorem Derives.unique {con : F T → T} {R : F J → J → Prop}
    (inj : ∀ l m : F T, con l = con m → l = m) (key : J → K)
    (det : ∀ (z : F (J × J)) (j j' : J), (∀ c ∈ children z, key c.1 = key c.2 → c.1 = c.2) →
      R (map Prod.fst z) j → R (map Prod.snd z) j' → key j = key j' → j = j')
    {t : T} {j : J} (h : Derives con R t j) :
    ∀ j', Derives con R t j' → key j = key j' → j = j' := by
  induction h with
  | node a j _ hra ih =>
    intro j' h' hk
    generalize ht : con (map Prod.fst a) = t at h'
    cases h' with
    | node a' _ hc' hra' =>
      obtain ⟨z, hza, hza', hz⟩ := zip Prod.fst Prod.fst a a' (inj _ _ ht)
      refine det (map (fun c : (T × J) × (T × J) => (c.1.2, c.2.2)) z) j j' ?_ ?_ ?_ hk
      · intro c hc
        rw [children_map] at hc
        obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
        have h1 : c0.1 ∈ children a := by rw [← hza]; exact mem_map_of_mem _ hc0
        have h2 : c0.2 ∈ children a' := by rw [← hza']; exact mem_map_of_mem _ hc0
        refine ih c0.1 h1 c0.2.2 ?_
        have := hc' c0.2 h2
        rw [← hz c0 hc0] at this; exact this
      · rw [← hza, map_map] at hra; rw [map_map]; exact hra
      · rw [← hza', map_map] at hra'; rw [map_map]; exact hra'

/-- Soundness of tables: every row of a valid table unfolds to a term, and
that term has an inductive derivation of the row's conclusion. -/
theorem Valid.derives [Nonempty T] {V : View ρ F J} {R : F J → J → Prop} (con : F T → T)
    {rows : Snoc ρ} (hv : Valid V R rows) {p : Int} {r : ρ} (hl : lookup ρ rows p = some r) :
    ∃ t, Unfolds V con rows p t ∧ Derives con R t (V.concl r) := by
  suffices h : ∀ (n : Nat) (p : Int) (r : ρ), p < n → lookup ρ rows p = some r →
      ∃ t, Unfolds V con rows p t ∧ Derives con R t (V.concl r) by
    have hb := Spec.Language.NamesAndScope.lookup_bound rows p r hl
    exact h (p.toNat + 1) p r (by omega) hl
  intro n
  induction n with
  | zero =>
    intro p r hp hl
    have := (Spec.Language.NamesAndScope.lookup_bound rows p r hl).1
    omega
  | succ n ih =>
    intro p r hp hl
    obtain ⟨a, hf, hra, hc⟩ := hv p r hl
    let tm : Int × J → T := fun c =>
      Classical.epsilon (fun t => Unfolds V con rows c.1 t ∧ Derives con R t c.2)
    have htm : ∀ c ∈ children a, Unfolds V con rows c.1 (tm c) ∧ Derives con R (tm c) c.2 := by
      intro c hcm
      obtain ⟨hlt, r', hl', hcl⟩ := hc c hcm
      obtain ⟨t, ht⟩ := ih c.1 r' (by omega) hl'
      rw [hcl] at ht
      exact Classical.epsilon_spec (p := fun t => Unfolds V con rows c.1 t ∧ Derives con R t c.2) ⟨t, ht⟩
    refine ⟨con (map tm a), ?_, ?_⟩
    · have h := Unfolds.node (V := V) (con := con) p r (map (fun c => (c.1, tm c)) a) hl
        (by rw [map_map]; exact hf)
        (by
          intro c hcm
          rw [children_map] at hcm
          obtain ⟨c0, h0, rfl⟩ := List.mem_map.1 hcm
          exact (htm c0 h0).1)
      rw [map_map] at h; exact h
    · have h := Derives.node (con := con) (R := R) (map (fun c => (tm c, c.2)) a) (V.concl r)
        (by
          intro c hcm
          rw [children_map] at hcm
          obtain ⟨c0, h0, rfl⟩ := List.mem_map.1 hcm
          exact (htm c0 h0).2)
        (by rw [map_map]; exact hra)
      rw [map_map] at h; exact h

/-- A table can be extended so that each of finitely many derivable
judgments has a row. -/
theorem tables_of_list {V : View ρ F J} {R : F J → J → Prop} {con : F T → T}
    (cs : List (T × J))
    (ih : ∀ c ∈ cs, ∀ rows, Valid V R rows → ∃ rows' r, Extends (Snoc.Extend rows' r) rows ∧
      Valid V R (Snoc.Extend rows' r) ∧ V.concl r = c.2 ∧
      Unfolds V con (Snoc.Extend rows' r) (length ρ rows') c.1) :
    ∀ rows, Valid V R rows → ∃ rows', Extends rows' rows ∧ Valid V R rows' ∧
      ∀ c ∈ cs, ∃ p r, lookup ρ rows' p = some r ∧ V.concl r = c.2 ∧ Unfolds V con rows' p c.1 := by
  induction cs with
  | nil => intro rows hv; exact ⟨rows, Extends.refl rows, hv, fun _ h => nomatch h⟩
  | cons c cs ihcs =>
    intro rows hv
    obtain ⟨rows1, he1, hv1, h1⟩ := ihcs (fun c hc => ih c (List.mem_cons_of_mem _ hc)) rows hv
    obtain ⟨rows2, r, he2, hv2, hcl, hu⟩ := ih c List.mem_cons_self rows1 hv1
    refine ⟨Snoc.Extend rows2 r, he2.trans he1, hv2, fun c' hc' => ?_⟩
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact ⟨length ρ rows2, r, by rw [lookup_extend, if_pos rfl], hcl, hu⟩
    · obtain ⟨p, r', hl, hcl', hu'⟩ := h1 c' hc'
      exact ⟨p, r', he2 _ _ hl, hcl', hu'.mono he2⟩

/-- Completeness of tables: every inductive derivation has a valid table,
extending any valid table, whose last row has the derivation's conclusion
and unfolds to its term. `mk` builds a row from its form and conclusion. -/
theorem Derives.table {V : View ρ F J} {R : F J → J → Prop} {con : F T → T}
    (mk : F Int → J → ρ) (hform : ∀ l j, V.form (mk l j) = l)
    (hconcl : ∀ l j, V.concl (mk l j) = j) {t : T} {j : J} (h : Derives con R t j) :
    ∀ rows, Valid V R rows → ∃ rows' r, Extends (Snoc.Extend rows' r) rows ∧
      Valid V R (Snoc.Extend rows' r) ∧ V.concl r = j ∧
      Unfolds V con (Snoc.Extend rows' r) (length ρ rows') t := by
  induction h with
  | node a j _ hra ih =>
    intro rows hv
    obtain ⟨rows', he, hv', hcs⟩ := tables_of_list (children a) ih rows hv
    let idx : T × J → Int := fun c => Classical.epsilon (fun p =>
      ∃ r, lookup ρ rows' p = some r ∧ V.concl r = c.2 ∧ Unfolds V con rows' p c.1)
    have hidx : ∀ c ∈ children a,
        ∃ r, lookup ρ rows' (idx c) = some r ∧ V.concl r = c.2 ∧ Unfolds V con rows' (idx c) c.1 :=
      fun c hc => Classical.epsilon_spec (p := fun p =>
        ∃ r, lookup ρ rows' p = some r ∧ V.concl r = c.2 ∧ Unfolds V con rows' p c.1) (hcs c hc)
    have hx := Extends.extend rows' (mk (map idx a) j)
    refine ⟨rows', mk (map idx a) j, hx.trans he, ?_, hconcl _ _, ?_⟩
    · rw [valid_extend]
      refine ⟨hv', map (fun c => (idx c, c.2)) a, ?_, ?_, ?_⟩
      · rw [map_map, hform]
      · rw [map_map, hconcl]; exact hra
      · intro c hc
        rw [children_map] at hc
        obtain ⟨c0, h0, rfl⟩ := List.mem_map.1 hc
        obtain ⟨r, hl, hcl, _⟩ := hidx c0 h0
        exact ⟨lookup_lt hl, r, hl, hcl⟩
    · have h := Unfolds.node (V := V) (con := con) (rows := Snoc.Extend rows' (mk (map idx a) j))
        (length ρ rows') (mk (map idx a) j) (map (fun c => (idx c, c.1)) a)
        (by rw [lookup_extend, if_pos rfl]) (by rw [map_map, hform])
        (by
          intro c hc
          rw [children_map] at hc
          obtain ⟨c0, h0, rfl⟩ := List.mem_map.1 hc
          obtain ⟨_, _, _, hu⟩ := hidx c0 h0
          exact hu.mono hx)
      rw [map_map] at h; exact h

/-- `Mapped σ con t t'`: `t'` is `t` with the layer map `σ` applied at every
node. -/
inductive Mapped (σ : (α : Type) → F α → F α) (con : F T → T) : T → T → Prop
  | node (z : F (T × T)) :
      (∀ c ∈ children z, Mapped σ con c.1 c.2) →
      Mapped σ con (con (map Prod.fst z)) (con (σ _ (map Prod.snd z)))

/-- A table whose rows are another's with their forms mapped by a natural
`σ` that adds no children unfolds, position by position, to the mapped
terms. -/
theorem Unfolds.mapped [Nonempty T] {V : View ρ F J} {V' : View ρ' F J'} {con : F T → T}
    (σ : (α : Type) → F α → F α)
    (natural : ∀ {α β : Type} (f : α → β) (l : F α), map f (σ _ l) = σ _ (map f l))
    (within : ∀ {α : Type} (l : F α), ∀ c ∈ children (σ _ l), c ∈ children l)
    {rows : Snoc ρ} {rows' : Snoc ρ'}
    (hrows : ∀ p r, lookup ρ rows p = some r →
      ∃ r', lookup ρ' rows' p = some r' ∧ V'.form r' = σ _ (V.form r))
    {p : Int} {t : T} (h : Unfolds V con rows p t) :
    ∃ t', Unfolds V' con rows' p t' ∧ Mapped σ con t t' := by
  induction h with
  | node p r a hl hf _ ih =>
    obtain ⟨r', hl', hf'⟩ := hrows p r hl
    let tm : Int × T → T := fun c =>
      Classical.epsilon (fun t' => Unfolds V' con rows' c.1 t' ∧ Mapped σ con c.2 t')
    have htm : ∀ c ∈ children a,
        Unfolds V' con rows' c.1 (tm c) ∧ Mapped σ con c.2 (tm c) := fun c hcm =>
      Classical.epsilon_spec
        (p := fun t' => Unfolds V' con rows' c.1 t' ∧ Mapped σ con c.2 t') (ih c hcm)
    refine ⟨con (σ _ (map tm a)), ?_, ?_⟩
    · have h := Unfolds.node (V := V') (con := con) p r' (σ _ (map (fun c => (c.1, tm c)) a)) hl'
        (by rw [natural, map_map, hf', ← hf])
        (by
          intro c hcm
          have hcm' := within _ c hcm
          rw [children_map] at hcm'
          obtain ⟨c0, h0, rfl⟩ := List.mem_map.1 hcm'
          exact (htm c0 h0).1)
      rw [natural, map_map] at h; exact h
    · have h := Mapped.node (σ := σ) (con := con) (map (fun c => (c.2, tm c)) a)
        (by
          intro c hcm
          rw [children_map] at hcm
          obtain ⟨c0, h0, rfl⟩ := List.mem_map.1 hcm
          exact (htm c0 h0).2)
      rw [map_map, map_map] at h; exact h

end
end Spec.Tables
