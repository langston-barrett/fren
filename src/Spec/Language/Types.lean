import Fren.Impl
import Fren.Literate

open Fren.Lang

#fren_md "Types.md"

set_option warningAsError true in
#fren_check

namespace Spec.Language.Types

open spec.types

/-! ## Lookup -/

theorem lookup_bound {α : Type} [Inhabited α] (xs : Snoc α) (level : Int) (x : α)
    (h : lookup _ xs level = some x) : 0 ≤ level ∧ level < length _ xs := by
  induction xs with
  | Empty => simp [lookup] at h
  | Extend earlier last ih =>
    simp only [lookup] at h
    simp only [length]
    split at h
    · rename_i eq; subst eq; omega
    · have := ih h; omega

theorem lookup_none {α : Type} [Inhabited α] (xs : Snoc α) (level : Int)
    (h : ¬ (0 ≤ level ∧ level < length _ xs)) : lookup _ xs level = none := by
  cases hl : lookup _ xs level with
  | none => rfl
  | some x => exact absurd (lookup_bound xs level x hl) h

/-! ## Arity -/

/-- Arguments and parameters correspond level by level, so their numbers agree. -/
theorem argument_types_length (args : Snoc Typing) (parameters : Snoc Ty)
    (h : argument_types? args parameters = true) :
    length _ args = length _ parameters := by
  induction args generalizing parameters with
  | Empty =>
    cases parameters with
    | Empty => rfl
    | Extend _ _ => simp [argument_types?] at h
  | Extend earlier arg ih =>
    cases parameters with
    | Empty => simp [argument_types?] at h
    | Extend earlierParameters parameter =>
      simp only [argument_types?, decide_eq_true_eq] at h
      simp [length, ih earlierParameters h.2]

/-! ## Tables -/

/-- The one-layer rule determines the type from the form and child typings. -/
theorem rule_unique (symbols : Snoc Entry) (context : Snoc Ty) (form : ExprF Typing) (a b : Ty)
    (ha : rule? symbols context form a = true) (hb : rule? symbols context form b = true) :
    a = b := by
  cases form with
  | Unary op operand =>
    cases op <;> simp [rule?, unary_rule?, unary_type?, fren_spec] at ha hb <;> simp_all
  | Binary op left right =>
    cases op <;> simp [rule?, binary_rule?, binary_type?, integer_binary?, comparison?,
      boolean_binary?, fren_spec] at ha hb <;> simp_all
  | Constructor item =>
    cases h : entry symbols item with
    | none => simp [rule?, constructor_rule?, h, fren_spec] at ha
    | some kind =>
      cases kind <;> simp [rule?, constructor_rule?, h, fren_spec] at ha hb <;> simp_all
  | Call item args =>
    cases h : entry symbols item with
    | none => simp [rule?, call_rule?, h, fren_spec] at ha
    | some kind =>
      cases kind <;> simp [rule?, call_rule?, h, fren_spec] at ha hb <;> simp_all
  | Match scrutinee arms =>
    rcases scrutinee with ⟨sc, sty⟩
    cases sty <;> cases arms <;>
      simp [rule?, match_rule?, fren_spec] at ha hb <;> simp_all
  | _ =>
    simp [rule?, boolean_rule?, integer_rule?, local_rule?, let_rule?, if_rule?,
      fren_spec] at ha hb <;> simp_all

/-- Every local of a valid table is in scope in its row's context. -/
theorem table_scoped (symbols : Snoc Entry) (rows : Snoc Row) (position level : Int) (r : Row)
    (valid : rows_valid? symbols rows = true) (found : lookup _ rows position = some r)
    (form : r.form = .Local level) : 0 ≤ level ∧ level < length _ r.context := by
  induction rows with
  | Empty => simp [lookup] at found
  | Extend earlier last ih =>
    simp only [lookup] at found
    split at found
    · have eq := Option.some.inj found
      subst eq
      rcases last with ⟨lform, lcontext, lty⟩
      simp only at form
      subst form
      simp [rows_valid?, rule?, local_rule?, fren_spec] at valid
      exact lookup_bound lcontext level lty valid.2
    · simp [rows_valid?, fren_spec] at valid
      exact ih valid.1 found

/-- Typing is deterministic: valid tables of the same shape are equal. -/
theorem table_unique (symbols : Snoc Entry) (left right : Snoc Row)
    (hl : rows_valid? symbols left = true) (hr : rows_valid? symbols right = true)
    (shape : same_shape? left right = true) : left = right := by
  induction left generalizing right with
  | Empty =>
    cases right with
    | Empty => rfl
    | Extend _ _ => simp [same_shape?] at shape
  | Extend earlier l ih =>
    cases right with
    | Empty => simp [same_shape?] at shape
    | Extend rearlier r =>
      simp only [same_shape?, decide_eq_true_eq] at shape
      obtain ⟨⟨hform, hcontext⟩, hrest⟩ := shape
      simp only [rows_valid?, decide_eq_true_eq] at hl hr
      have heq := ih rearlier hl.1 hr.1 hrest
      subst heq
      rcases l with ⟨lf, lc, lt⟩
      rcases r with ⟨rf, rc, rt⟩
      simp only at hform hcontext
      subst hform; subst hcontext
      have hl2 := hl.2
      have hr2 := hr.2
      simp only at hl2 hr2
      cases ha : annotate earlier lf with
      | none => simp [ha] at hl2
      | some form =>
        simp only [ha] at hl2 hr2
        rw [rule_unique symbols lc form lt rt hl2 hr2]

theorem insert_length (context : Snoc Ty) (cutoff : Int) (extra : Ty) (h0 : 0 ≤ cutoff)
    (h : cutoff ≤ length _ context) :
    length _ (insert_type context cutoff extra) = length _ context + 1 := by
  induction context with
  | Empty =>
    simp [length] at h
    simp [insert_type, length, show cutoff = 0 by omega]
  | Extend earlier ty ih =>
    simp only [length] at h
    simp only [insert_type]
    split
    · simp [length]
    · rename_i hne
      simp only [length]
      rw [ih (by push_cast at hne; omega)]

/-- Weakening's step for locals: inserting a type at a level and shifting
levels preserves every lookup, and the inserted level holds the new type. -/
theorem lookup_shift (context : Snoc Ty) (cutoff : Int) (extra : Ty) (h0 : 0 ≤ cutoff)
    (h : cutoff ≤ length _ context) :
    (∀ level, lookup _ (insert_type context cutoff extra) (shift level cutoff) =
      lookup _ context level) ∧
    lookup _ (insert_type context cutoff extra) cutoff = some extra := by
  induction context with
  | Empty =>
    simp [length] at h
    have hc : cutoff = 0 := by omega
    subst hc
    refine ⟨fun level => ?_, ?_⟩
    · by_cases hl : level ≥ 0
      · have hs : shift level 0 = level + 1 := by simp [shift, hl]
        rw [hs]; simp [insert_type, lookup, length]; omega
      · have hs : shift level 0 = level := by simp [shift]; omega
        rw [hs]; simp [insert_type, lookup, length]; omega
    · simp [insert_type, lookup, length]
  | Extend earlier ty ih =>
    simp only [length] at h
    push_cast at h
    by_cases hc : cutoff = ↑(length _ earlier) + 1
    · have hins : insert_type (.Extend earlier ty) cutoff extra = .Extend (.Extend earlier ty) extra := by
        simp [insert_type, hc]
      rw [hins]
      refine ⟨fun level => ?_, ?_⟩
      · by_cases hl : level ≥ cutoff
        · have hs : shift level cutoff = level + 1 := by simp [shift, hl]
          rw [hs]
          have n1 : lookup _ earlier (level + 1) = none := lookup_none _ _ (by omega)
          have n2 : lookup _ earlier level = none := lookup_none _ _ (by omega)
          simp [lookup, length, n1, n2, show ¬ (level = ↑(length Ty earlier)) by omega,
            show ¬ (level + 1 = ↑(length Ty earlier)) by omega]
        · have hs : shift level cutoff = level := by simp [shift]; omega
          rw [hs]
          simp [lookup, length]
          omega
      · simp [lookup, length, hc]
    · have hle : cutoff ≤ ↑(length _ earlier) := by omega
      have hins : insert_type (.Extend earlier ty) cutoff extra =
          .Extend (insert_type earlier cutoff extra) ty := by
        simp [insert_type]; push_cast; simp [hc]
      have hlen := insert_length earlier cutoff extra h0 hle
      obtain ⟨ih1, ih2⟩ := ih hle
      rw [hins]
      refine ⟨fun level => ?_, ?_⟩
      · simp only [lookup, hlen]
        by_cases e : level = ↑(length Ty earlier)
        · have hs : shift level cutoff = level + 1 := by simp [shift]; omega
          rw [hs, if_pos (by push_cast; omega), if_pos e]
        · have hs : ¬ (shift level cutoff = ↑(length Ty earlier + 1)) := by
            simp only [shift]; push_cast; split <;> omega
          rw [if_neg hs, if_neg e]; exact ih1 level
      · simp only [lookup, hlen]
        rw [if_neg (by push_cast; omega)]; exact ih2

/-! ## Regularity -/

theorem lookup_ok (symbols : Snoc Entry) (context : Snoc Ty) (level : Int) (ty : Ty)
    (hc : context_ok? symbols context = true) (h : lookup _ context level = some ty) :
    type_ok? symbols ty = true := by
  induction context with
  | Empty => simp [lookup] at h
  | Extend earlier last ih =>
    simp only [context_ok?, decide_eq_true_eq] at hc
    simp only [lookup] at h
    split at h
    · have := Option.some.inj h; subst this
      have h1 := hc.1
      cases last <;> simp_all [type_ok?, fren_spec]
    · exact ih hc.2 h

theorem entry_kind_ok (symbols bindings : Snoc Entry) (item : Fren.Seq String) (kind : ItemKind)
    (hb : bindings_ok? symbols bindings = true) (h : entry bindings item = some kind) :
    (∀ owner, kind = .Constructor owner → type_ok? symbols (.Nominal owner) = true) ∧
    (∀ signature, kind = .Function signature → type_ok? symbols signature.result = true) := by
  induction bindings with
  | Empty => simp [entry] at h
  | Extend earlier last ih =>
    simp only [bindings_ok?, decide_eq_true_eq] at hb
    simp only [entry] at h
    split at h
    · have := Option.some.inj h; subst this
      rcases last with ⟨litem, lkind⟩
      have h2 := hb.1.2
      constructor
      · intro owner hk
        simp only at hk; subst hk
        simp only [type_ok?]
        cases he : entry symbols owner with
        | none => simp [he, fren_spec] at h2
        | some k => cases k <;> simp [he, fren_spec] at h2 ⊢
      · intro signature hk
        simp only at hk; subst hk
        simp [fren_spec] at h2
        have h3 := h2.2
        generalize signature.result = t at h3 ⊢
        cases t <;> simp [type_ok?, fren_spec] at h3 ⊢
        exact h3
    · exact ih hb.2 h

/-- A constructor's owner, and a function's result, are well formed. -/
theorem entry_types_ok (symbols : Snoc Entry) (item : Fren.Seq String) (hs : symbols_ok? symbols = true) :
    (∀ owner, entry symbols item = some (.Constructor owner) → type_ok? symbols (.Nominal owner) = true) ∧
    (∀ signature, entry symbols item = some (.Function signature) →
      type_ok? symbols signature.result = true) := by
  have hs' : bindings_ok? symbols symbols = true := by simpa [symbols_ok?] using hs
  exact ⟨fun owner h => (entry_kind_ok symbols symbols item _ hs' h).1 owner rfl,
    fun signature h => (entry_kind_ok symbols symbols item _ hs' h).2 signature rfl⟩

theorem typings_ok_extend (symbols : Snoc Entry) (earlier : Snoc Typing) (t : Typing) :
    typings_ok? symbols (.Extend earlier t) = true ↔
      type_ok? symbols t.ty = true ∧ typings_ok? symbols earlier = true := by
  rcases t with ⟨c, ty⟩
  cases ty <;> simp [typings_ok?, type_ok?, fren_spec]

/-- One layer: a typed layer over well-formed children has a well-formed type. -/
theorem layer_regular (symbols : Snoc Entry) (context : Snoc Ty) (form : ExprF Typing) (ty : Ty)
    (hs : symbols_ok? symbols = true) (hc : context_ok? symbols context = true)
    (hch : children_ok? symbols form = true) (h : rule? symbols context form ty = true) :
    type_ok? symbols ty = true := by
  simp only [children_ok?, decide_eq_true_eq] at hch
  cases form with
  | BooleanLiteral _ => simp [rule?, boolean_rule?] at h; subst h; rfl
  | IntegerLiteral _ => simp [rule?, integer_rule?] at h; subst h; rfl
  | Local level =>
    simp [rule?, local_rule?, fren_spec] at h
    exact lookup_ok symbols context level ty hc h
  | Constructor item =>
    cases he : entry symbols item with
    | none => simp [rule?, constructor_rule?, he, fren_spec] at h
    | some kind =>
      cases kind with
      | Constructor owner =>
        simp [rule?, constructor_rule?, he, fren_spec] at h
        subst h
        exact (entry_types_ok symbols item hs).1 owner he
      | _ => simp [rule?, constructor_rule?, he, fren_spec] at h
  | Unary op operand =>
    cases op <;> simp [rule?, unary_rule?, unary_type?, fren_spec] at h <;>
      simp [h, type_ok?, fren_spec]
  | Binary op left right =>
    cases op <;> simp [rule?, binary_rule?, binary_type?, integer_binary?, comparison?,
      boolean_binary?, fren_spec] at h <;> (rw [h.2.2]; rfl)
  | Call item args =>
    cases he : entry symbols item with
    | none => simp [rule?, call_rule?, he, fren_spec] at h
    | some kind =>
      cases kind with
      | Function signature =>
        simp [rule?, call_rule?, he, fren_spec] at h
        rw [h.1.1]
        exact (entry_types_ok symbols item hs).2 signature he
      | _ => simp [rule?, call_rule?, he, fren_spec] at h
  | Let annotation value body =>
    simp [rule?, let_rule?, fren_spec] at h
    simp only [children, two, one] at hch
    rw [← h.2]
    exact ((typings_ok_extend _ _ _).1 hch).1
  | If condition t e =>
    simp [rule?, if_rule?, fren_spec] at h
    simp only [children, three, two, one] at hch
    rw [← h.1.1.2]
    exact ((typings_ok_extend _ _ _).1 ((typings_ok_extend _ _ _).1 hch).2).1
  | Match scrutinee arms =>
    cases arms with
    | Empty => simp [rule?, match_rule?, fren_spec] at h
    | Extend earlier last =>
      simp [rule?, match_rule?, arm_bodies?, fren_spec] at h
      simp only [children, arm_typings] at hch
      rw [← h.1.2.1.2]
      exact ((typings_ok_extend _ _ _).1 ((typings_ok_extend _ _ _).1 hch).2).1

theorem typing_at_row (rows : Snoc Row) (position : Int) (t : Typing)
    (h : typing_at rows position = some t) :
    ∃ r, lookup _ rows position = some r ∧ t.ty = r.ty := by
  simp only [typing_at] at h
  cases hl : lookup _ rows position with
  | none => simp [hl, fren_spec] at h
  | some r =>
    simp [hl, fren_spec] at h
    exact ⟨r, rfl, by rw [← h]⟩

theorem annotate_arguments_ok (symbols : Snoc Entry) (rows : Snoc Row)
    (child : ∀ p t, typing_at rows p = some t → type_ok? symbols t.ty = true)
    (args : Snoc Int) (typed : Snoc Typing) (h : annotate_arguments rows args = some typed) :
    typings_ok? symbols typed = true := by
  induction args generalizing typed with
  | Empty => simp [annotate_arguments, fren_spec] at h; subst h; rfl
  | Extend earlier arg ih =>
    simp only [annotate_arguments] at h
    cases ha : annotate_arguments rows earlier with
    | none => simp [ha, fren_spec] at h
    | some te =>
      cases ht : typing_at rows arg with
      | none => simp [ha, ht, fren_spec] at h
      | some t =>
        simp [ha, ht, fren_spec] at h
        subst h
        exact (typings_ok_extend _ _ _).2 ⟨child arg t ht, ih te ha⟩

theorem annotate_arms_ok (symbols : Snoc Entry) (rows : Snoc Row)
    (child : ∀ p t, typing_at rows p = some t → type_ok? symbols t.ty = true)
    (arms : Snoc (ArmF Int)) (typed : Snoc (ArmF Typing)) (h : annotate_arms rows arms = some typed) :
    typings_ok? symbols (arm_typings typed) = true := by
  induction arms generalizing typed with
  | Empty => simp [annotate_arms, fren_spec] at h; subst h; rfl
  | Extend earlier arm ih =>
    simp only [annotate_arms] at h
    cases ha : annotate_arms rows earlier with
    | none => simp [ha, fren_spec] at h
    | some te =>
      cases ht : typing_at rows arm.body with
      | none => simp [ha, ht, fren_spec] at h
      | some t =>
        simp [ha, ht, fren_spec] at h
        subst h
        simp only [arm_typings]
        exact (typings_ok_extend _ _ _).2 ⟨child arm.body t ht, ih te ha⟩

/-- Every child typing that a table supplies has a well-formed type. -/
theorem annotate_children_ok (symbols : Snoc Entry) (rows : Snoc Row)
    (ok : ∀ p r, lookup _ rows p = some r → type_ok? symbols r.ty = true)
    (form : ExprF Int) (typed : ExprF Typing) (h : annotate rows form = some typed) :
    children_ok? symbols typed = true := by
  have child : ∀ p t, typing_at rows p = some t → type_ok? symbols t.ty = true := by
    intro p t ht
    obtain ⟨r, hr, hty⟩ := typing_at_row rows p t ht
    rw [hty]; exact ok p r hr
  have ext := typings_ok_extend symbols
  have empty : typings_ok? symbols .Empty = true := by simp [typings_ok?]
  simp only [children_ok?, decide_eq_true_eq]
  cases form with
  | Call item args =>
    simp only [annotate] at h
    cases ha : annotate_arguments rows args with
    | none => simp [ha, fren_spec] at h
    | some te =>
      simp [ha, fren_spec] at h; subst h
      simp only [children]
      exact annotate_arguments_ok symbols rows child args te ha
  | Match scrutinee arms =>
    simp only [annotate] at h
    cases hs : typing_at rows scrutinee with
    | none => simp [hs, fren_spec] at h
    | some ts =>
      cases ha : annotate_arms rows arms with
      | none => simp [hs, ha, fren_spec] at h
      | some ta =>
        simp [hs, ha, fren_spec] at h; subst h
        simp only [children]
        exact (ext _ _).2 ⟨child scrutinee ts hs, annotate_arms_ok symbols rows child arms ta ha⟩
  | Unary op operand =>
    simp only [annotate] at h
    cases h1 : typing_at rows operand with
    | none => simp [h1, fren_spec] at h
    | some t1 =>
      simp [h1, fren_spec] at h; subst h
      simp only [children, one]
      exact (ext _ _).2 ⟨child _ _ h1, empty⟩
  | Binary op l r =>
    simp only [annotate] at h
    cases h1 : typing_at rows l with
    | none => simp [h1, fren_spec] at h
    | some t1 =>
      cases h2 : typing_at rows r with
      | none => simp [h1, h2, fren_spec] at h
      | some t2 =>
        simp [h1, h2, fren_spec] at h; subst h
        simp only [children, two, one]
        exact (ext _ _).2 ⟨child _ _ h2, (ext _ _).2 ⟨child _ _ h1, empty⟩⟩
  | Let annotation v b =>
    simp only [annotate] at h
    cases h1 : typing_at rows v with
    | none => simp [h1, fren_spec] at h
    | some t1 =>
      cases h2 : typing_at rows b with
      | none => simp [h1, h2, fren_spec] at h
      | some t2 =>
        simp [h1, h2, fren_spec] at h; subst h
        simp only [children, two, one]
        exact (ext _ _).2 ⟨child _ _ h2, (ext _ _).2 ⟨child _ _ h1, empty⟩⟩
  | If c t e =>
    simp only [annotate] at h
    cases h1 : typing_at rows c with
    | none => simp [h1, fren_spec] at h
    | some t1 =>
      cases h2 : typing_at rows t with
      | none => simp [h1, h2, fren_spec] at h
      | some t2 =>
        cases h3 : typing_at rows e with
        | none => simp [h1, h2, h3, fren_spec] at h
        | some t3 =>
          simp [h1, h2, h3, fren_spec] at h; subst h
          simp only [children, three, two, one]
          exact (ext _ _).2 ⟨child _ _ h3, (ext _ _).2 ⟨child _ _ h2, (ext _ _).2 ⟨child _ _ h1, empty⟩⟩⟩
  | _ => simp [annotate, fren_spec] at h; subst h; rfl

/-- Over a well-formed environment, every row of a valid table whose contexts
are well formed has a well-formed type. -/
theorem table_regular (symbols : Snoc Entry) (rows : Snoc Row)
    (hs : symbols_ok? symbols = true) (hv : rows_valid? symbols rows = true)
    (hc : contexts_ok? symbols rows = true) :
    ∀ p r, lookup _ rows p = some r → type_ok? symbols r.ty = true := by
  induction rows with
  | Empty => intro p r h; simp [lookup] at h
  | Extend earlier last ih =>
    simp only [rows_valid?, decide_eq_true_eq] at hv
    simp only [contexts_ok?, decide_eq_true_eq] at hc
    have ok := ih hv.1 hc.2
    intro p r h
    simp only [lookup] at h
    split at h
    · have := Option.some.inj h; subst this
      have hl := hv.2
      cases ha : annotate earlier last.form with
      | none => simp [ha] at hl
      | some form =>
        simp only [ha] at hl
        exact layer_regular symbols last.context form last.ty hs hc.1
          (annotate_children_ok symbols earlier ok last.form form ha) hl
    · exact ok p r h

/-! ## Weakening -/

theorem insert_extend (context : Snoc Ty) (cutoff : Int) (extra ty : Ty)
    (h : cutoff ≤ length _ context) :
    insert_type (.Extend context ty) cutoff extra = .Extend (insert_type context cutoff extra) ty := by
  simp only [insert_type]
  rw [if_neg (by omega)]

theorem in_context_weaken (args : Snoc Typing) (context : Snoc Ty) (cutoff : Int) (extra : Ty)
    (h : in_context? args context = true) :
    in_context? (weaken_typings args cutoff extra) (insert_type context cutoff extra) = true := by
  induction args with
  | Empty => rfl
  | Extend earlier arg ih =>
    simp only [in_context?, decide_eq_true_eq] at h
    simp only [weaken_typings, weaken_typing, in_context?, decide_eq_true_eq]
    exact ⟨by rw [h.1], ih h.2⟩

theorem argument_types_weaken (args : Snoc Typing) (parameters : Snoc Ty) (cutoff : Int) (extra : Ty)
    (h : argument_types? args parameters = true) :
    argument_types? (weaken_typings args cutoff extra) parameters = true := by
  induction args generalizing parameters with
  | Empty => cases parameters <;> simp_all [argument_types?, weaken_typings]
  | Extend earlier arg ih =>
    cases parameters with
    | Empty => simp [argument_types?] at h
    | Extend ps p =>
      simp only [argument_types?, decide_eq_true_eq] at h
      simp only [weaken_typings, weaken_typing, argument_types?, decide_eq_true_eq]
      exact ⟨h.1, ih ps h.2⟩

theorem arm_bodies_weaken (arms : Snoc (ArmF Typing)) (context : Snoc Ty) (ty : Ty) (cutoff : Int)
    (extra : Ty) (h : arm_bodies? arms context ty = true) :
    arm_bodies? (weaken_arms arms cutoff extra) (insert_type context cutoff extra) ty = true := by
  induction arms with
  | Empty => rfl
  | Extend earlier arm ih =>
    simp only [arm_bodies?, decide_eq_true_eq] at h
    simp only [weaken_arms, weaken_typing, arm_bodies?, decide_eq_true_eq]
    exact ⟨⟨by rw [h.1.1], h.1.2⟩, ih h.2⟩

theorem arm_patterns_weaken (symbols : Snoc Entry) (arms : Snoc (ArmF Typing)) (owner : Fren.Seq String)
    (cutoff : Int) (extra : Ty) (h : arm_patterns? symbols arms owner = true) :
    arm_patterns? symbols (weaken_arms arms cutoff extra) owner = true := by
  induction arms with
  | Empty => rfl
  | Extend earlier arm ih =>
    simp only [arm_patterns?, decide_eq_true_eq] at h
    simp only [weaken_arms, arm_patterns?, decide_eq_true_eq]
    exact ⟨h.1, ih h.2⟩

/-- One layer: inserting a type at level `cutoff` and shifting levels keeps a
layer typed. -/
theorem layer_weakening (symbols : Snoc Entry) (context : Snoc Ty) (form : ExprF Typing) (ty : Ty)
    (cutoff : Int) (extra : Ty) (h0 : 0 ≤ cutoff) (hn : cutoff ≤ length _ context)
    (h : rule? symbols context form ty = true) :
    rule? symbols (insert_type context cutoff extra) (weaken_layer form cutoff extra) ty = true := by
  cases form with
  | Local level =>
    simp [rule?, local_rule?, fren_spec] at h ⊢
    rw [(lookup_shift context cutoff extra h0 hn).1 level]; exact h
  | Let annotation value body =>
    simp [rule?, let_rule?, fren_spec] at h ⊢
    obtain ⟨⟨⟨hv, ha⟩, hb⟩, hty⟩ := h
    refine ⟨⟨⟨by rw [hv], ha⟩, ?_⟩, hty⟩
    rw [hb, insert_extend context cutoff extra value.ty hn]
  | Call item args =>
    have hi := in_context_weaken args context cutoff extra
    cases he : entry symbols item with
    | none => simp [rule?, call_rule?, he, fren_spec] at h
    | some kind =>
      cases kind with
      | Function signature =>
        have ha := argument_types_weaken args signature.parameters cutoff extra
        simp [rule?, call_rule?, he, fren_spec] at h ⊢
        exact ⟨⟨h.1.1, hi h.1.2⟩, ha h.2⟩
      | _ => simp [rule?, call_rule?, he, fren_spec] at h
  | Match scrutinee arms =>
    have hb := arm_bodies_weaken arms context ty cutoff extra
    rcases scrutinee with ⟨sc, sty⟩
    cases sty with
    | Nominal owner =>
      have hp := arm_patterns_weaken symbols arms owner cutoff extra
      cases arms with
      | Empty => simp [rule?, match_rule?, fren_spec] at h
      | Extend earlier last =>
        simp only [rule?, match_rule?, weaken_typing, weaken_arms, decide_eq_true_eq] at h ⊢
        simp only [weaken_arms, weaken_typing] at hb hp
        exact ⟨⟨⟨by rw [h.1.1.1], by simp⟩, hb h.1.2⟩, hp h.2⟩
    | _ => simp [rule?, match_rule?, fren_spec] at h
  | _ =>
    simp [rule?, boolean_rule?, integer_rule?, constructor_rule?, unary_rule?, binary_rule?,
      if_rule?, fren_spec] at h ⊢
    first | exact h | simp_all

/-- A row with σ inserted at level `cutoff` of its context and its local shifted. -/
def weakenRow (cutoff : Int) (extra : Ty) (r : Row) : Row :=
  { form := shift_form r.form cutoff, context := insert_type r.context cutoff extra, ty := r.ty }

theorem length_weaken (rows : Snoc Row) (cutoff : Int) (extra : Ty) :
    length _ (weaken rows cutoff extra) = length _ rows := by
  induction rows with
  | Empty => rfl
  | Extend earlier last ih => simp [weaken, length, ih]

theorem lookup_weaken (rows : Snoc Row) (cutoff : Int) (extra : Ty) (p : Int) :
    lookup _ (weaken rows cutoff extra) p = (lookup _ rows p).map (weakenRow cutoff extra) := by
  induction rows with
  | Empty => rfl
  | Extend earlier last ih =>
    simp only [weaken, lookup, length_weaken]
    split <;> simp_all [weakenRow]

theorem typing_at_weaken (rows : Snoc Row) (cutoff : Int) (extra : Ty) (p : Int) :
    typing_at (weaken rows cutoff extra) p =
      (typing_at rows p).map (fun t => weaken_typing t cutoff extra) := by
  simp only [typing_at, lookup_weaken]
  cases lookup _ rows p <;> simp [weakenRow, weaken_typing, fren_spec]

theorem annotate_arguments_weaken (rows : Snoc Row) (cutoff : Int) (extra : Ty) (args : Snoc Int) :
    annotate_arguments (weaken rows cutoff extra) args =
      (annotate_arguments rows args).map (fun ts => weaken_typings ts cutoff extra) := by
  induction args with
  | Empty => rfl
  | Extend earlier arg ih =>
    simp only [annotate_arguments, ih, typing_at_weaken]
    cases annotate_arguments rows earlier <;> cases typing_at rows arg <;> simp [weaken_typings]

theorem annotate_arms_weaken (rows : Snoc Row) (cutoff : Int) (extra : Ty) (arms : Snoc (ArmF Int)) :
    annotate_arms (weaken rows cutoff extra) arms =
      (annotate_arms rows arms).map (fun ts => weaken_arms ts cutoff extra) := by
  induction arms with
  | Empty => rfl
  | Extend earlier arm ih =>
    simp only [annotate_arms, ih, typing_at_weaken]
    cases annotate_arms rows earlier <;> cases typing_at rows arm.body <;> simp [weaken_arms]

theorem annotate_weaken (rows : Snoc Row) (cutoff : Int) (extra : Ty) (form : ExprF Int) :
    annotate (weaken rows cutoff extra) (shift_form form cutoff) =
      (annotate rows form).map (fun f => weaken_layer f cutoff extra) := by
  cases form with
  | Unary op a =>
    simp only [annotate, typing_at_weaken]
    cases typing_at rows a <;> first | rfl | simp [weaken_layer, fren_spec]
  | Binary op a b =>
    simp only [annotate, typing_at_weaken]
    cases typing_at rows a <;> cases typing_at rows b <;> first | rfl | simp [weaken_layer, fren_spec]
  | Call item args =>
    simp only [annotate, annotate_arguments_weaken]
    cases annotate_arguments rows args <;> first | rfl | simp [weaken_layer, fren_spec]
  | Let annotation a b =>
    simp only [annotate, typing_at_weaken]
    cases typing_at rows a <;> cases typing_at rows b <;> first | rfl | simp [weaken_layer, fren_spec]
  | If a b c =>
    simp only [annotate, typing_at_weaken]
    cases typing_at rows a <;> cases typing_at rows b <;> cases typing_at rows c <;>
      first | rfl | simp [weaken_layer, fren_spec]
  | Match a arms =>
    simp only [annotate, typing_at_weaken, annotate_arms_weaken]
    cases typing_at rows a <;> cases annotate_arms rows arms <;> first | rfl | simp [weaken_layer, fren_spec]
  | _ => simp [annotate, weaken_layer, fren_spec]

/-- Weakening a valid table whose row contexts reach the cutoff keeps it valid. -/
theorem table_weakening (symbols : Snoc Entry) (rows : Snoc Row) (cutoff : Int) (extra : Ty)
    (h0 : 0 ≤ cutoff) (hv : rows_valid? symbols rows = true)
    (hr : contexts_reach? rows cutoff = true) :
    rows_valid? symbols (weaken rows cutoff extra) = true := by
  induction rows with
  | Empty => rfl
  | Extend earlier last ih =>
    simp only [rows_valid?, decide_eq_true_eq] at hv
    simp only [contexts_reach?, decide_eq_true_eq] at hr
    simp only [weaken, rows_valid?, decide_eq_true_eq]
    refine ⟨ih hv.1 hr.2, ?_⟩
    have hl := hv.2
    have ha := annotate_weaken earlier cutoff extra last.form
    cases hf : annotate earlier last.form with
    | none => simp [hf] at hl
    | some form =>
      simp only [hf] at hl ha
      simp only [ha, Option.map]
      exact layer_weakening symbols last.context form last.ty cutoff extra h0 hr.1.2 hl

/-! ## Examples -/

/-- The chapter's worked derivations. -/
theorem worked_examples :
    OLDEST_LEVEL_EXAMPLE = true ∧ LET_EXAMPLE = true ∧ MATCH_EXAMPLE = true ∧
    CALL_EXAMPLE = true ∧ PROGRAM_EXAMPLE = true := by
  decide

/-- Snoc sequences of one to four entries, oldest first. -/
abbrev t1 {α : Type} (a : α) : Snoc α := .Extend .Empty a
abbrev t2 {α : Type} (a b : α) : Snoc α := .Extend (t1 a) b
abbrev t3 {α : Type} (a b c : α) : Snoc α := .Extend (t2 a b) c
abbrev t4 {α : Type} (a b c d : α) : Snoc α := .Extend (t3 a b c) d

/-- Typed in the empty context at `ty` against the example environment. -/
abbrev typed (rows : Snoc Row) (ty : Ty) : Bool := derivation? SYMBOLS rows .Empty ty

abbrev int (n : Int) : Row := row (.IntegerLiteral n) .Empty .Integer
abbrev bool (b : Bool) : Row := row (.BooleanLiteral b) .Empty .Boolean
abbrev red : Row := row (.Constructor LIGHT_RED) .Empty (.Nominal LIGHT)
abbrev arm (c : Fren.Seq String) (body : Int) : ArmF Int := ⟨c, body⟩

-- ⊢ 7 : Integer, and not at Boolean.
example : typed (t1 (int 7)) .Integer = true := by decide
example : typed (t1 (row (.IntegerLiteral 7) .Empty .Boolean)) .Boolean = false := by decide
-- ⊢ true : Boolean.
example : typed (t1 (bool true)) .Boolean = true := by decide
-- Rejected: · ⊢ #0, which has no entry.
example : typed (t1 (row (.Local 0) .Empty .Integer)) .Integer = false := by decide
-- ·, Boolean, Integer ⊢ #1 : Integer.
example : derivation? SYMBOLS (t1 (row (.Local 1) BOOLEAN_INTEGER .Integer))
    BOOLEAN_INTEGER .Integer = true := by decide
-- ⊢ -1 : Integer, and rejected: -true.
example : typed (t2 (int 1) (row (.Unary .Neg 0) .Empty .Integer)) .Integer = true := by decide
example : typed (t2 (bool true) (row (.Unary .Neg 0) .Empty .Integer)) .Integer = false := by decide
-- ⊢ not true : Boolean.
example : typed (t2 (bool true) (row (.Unary .Not 0) .Empty .Boolean)) .Boolean = true := by decide
-- Rejected: a child row that does not exist.
example : typed (t1 (row (.Unary .Neg 0) .Empty .Integer)) .Integer = false := by decide
-- ⊢ 1 + 2 : Integer; rejected: false + 2.
example : typed (t3 (int 1) (int 2) (row (.Binary .Add 0 1) .Empty .Integer)) .Integer = true := by
  decide
example : typed (t3 (bool false) (int 2) (row (.Binary .Add 0 1) .Empty .Integer)) .Integer =
    false := by decide
-- ⊢ 1 < 2 : Boolean.
example : typed (t3 (int 1) (int 2) (row (.Binary .Lt 0 1) .Empty .Boolean)) .Boolean = true := by
  decide
-- Rejected: the right operand of `and` is checked even when the left is false.
example : typed (t3 (bool false) (row (.Local 0) .Empty .Boolean)
    (row (.Binary .And 0 1) .Empty .Boolean)) .Boolean = false := by decide
-- ⊢ M::Light::Red = M::Light::Red : Boolean; rejected across enumerations.
example : typed (t3 red red (row (.Binary .Eq 0 1) .Empty .Boolean)) .Boolean = true := by decide
example : typed (t3 red (row (.Constructor SIGNAL_RED) .Empty (.Nominal SIGNAL))
    (row (.Binary .Eq 0 1) .Empty .Boolean)) .Boolean = false := by decide
-- ⊢ let 1 in #0 : Integer, without an annotation; rejected with annotation Boolean.
example : typed (t3 (int 1) (row (.Local 0) (.Extend .Empty .Integer) .Integer)
    (row (.Let none 0 1) .Empty .Integer)) .Integer = true := by decide
example : typed (t3 (int 1) (row (.Local 0) (.Extend .Empty .Integer) .Integer)
    (row (.Let (some .Boolean) 0 1) .Empty .Integer)) .Integer = false := by decide
-- ·, Boolean ⊢ let 1 in #1 : Integer: the binder has level |Γ| = 1.
example : derivation? SYMBOLS
    (t3 (row (.IntegerLiteral 1) (.Extend .Empty .Boolean) .Integer)
      (row (.Local 1) BOOLEAN_INTEGER .Integer)
      (row (.Let none 0 1) (.Extend .Empty .Boolean) .Integer))
    (.Extend .Empty .Boolean) .Integer = true := by decide
-- ⊢ if true then 1 else 2 : Integer; rejected: if 0 then 1 else 2.
example : typed (t4 (bool true) (int 1) (int 2) (row (.If 0 1 2) .Empty .Integer))
    .Integer = true := by decide
example : typed (t4 (int 0) (int 1) (int 2) (row (.If 0 1 2) .Empty .Integer))
    .Integer = false := by decide
-- Rejected: a match with no arms.
example : typed (t2 red (row (.Match 0 .Empty) .Empty .Integer)) .Integer = false := by decide
-- Rejected: one arm body of the wrong type.
example : typed (t4 red (int 1) (bool true)
    (row (.Match 0 (.Extend (.Extend .Empty (arm LIGHT_RED 1)) (arm LIGHT_GREEN 2))) .Empty .Integer))
    .Integer = false := by decide
-- Rejected: an argument of the wrong type, M::f(true).
example : typed (t2 (bool true) (row (.Call F (.Extend .Empty 0)) .Empty .Integer)) .Integer =
    false := by decide
-- Rejected: a constructor is not callable, and a function is not a value.
example : typed (t2 (int 1) (row (.Call LIGHT_RED (.Extend .Empty 0)) .Empty .Integer)) .Integer =
    false := by decide
example : typed (t1 (row (.Constructor F) .Empty .Integer)) .Integer = false := by decide
-- Rejected: a constructor typed at another type than its owner.
example : typed (t1 (row (.Constructor LIGHT_RED) .Empty .Integer)) .Integer = false := by decide
-- A duplicate binding makes an environment ill formed.
example : symbols_ok? (.Extend SYMBOLS (bind F (.Constructor LIGHT))) = false := by decide
-- A constructor's owner must list it.
example : symbols_ok? (.Extend .Empty (bind LIGHT_RED (.Constructor LIGHT))) = false := by decide
-- The `?` suffix rule.
example : parameter_type? none true .Boolean = true := by decide
example : parameter_type? none false .Boolean = false := by decide
example : parameter_type? (some .Integer) true .Integer = false := by decide
example : let_annotation? none true (some .Boolean) = true := by decide

-- A program needs exactly one body for each function: none and two are rejected.
example : program_ok? SYMBOLS .Empty = false := by decide
example : program_ok? SYMBOLS (.Extend (.Extend .Empty
    (.Function F (t1 (row (.Local 0) (.Extend .Empty .Integer) .Integer))))
    (.Function F (t1 (row (.Local 0) (.Extend .Empty .Integer) .Integer)))) = false := by decide
example : program_ok? SYMBOLS (.Extend .Empty
    (.Function F (t1 (row (.Local 0) (.Extend .Empty .Integer) .Integer)))) = true := by decide

-- Rejected: no judgment holds in an ill-formed environment or context.
example : derivation? (.Extend .Empty (bind LIGHT_RED (.Constructor LIGHT))) (t1 (int 7))
    .Empty .Integer = false := by decide
example : derivation? SYMBOLS (t1 (row (.Local 0) (t1 (.Nominal LIGHT_RED)) (.Nominal LIGHT_RED)))
    (t1 (.Nominal LIGHT_RED)) (.Nominal LIGHT_RED) = false := by decide

/-- Typing accepts a match that omits a constructor or repeats one. -/
theorem coverage_separate :
    typed (t3 red (int 1) (row (.Match 0 (.Extend .Empty (arm LIGHT_RED 1))) .Empty .Integer))
      .Integer = true ∧
    typed (t3 red (int 1)
      (row (.Match 0 (.Extend (.Extend .Empty (arm LIGHT_RED 1)) (arm LIGHT_RED 1))) .Empty .Integer))
      .Integer = true := by
  decide

end Spec.Language.Types
