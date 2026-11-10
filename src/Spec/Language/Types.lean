import Fren.Impl
import Fren.Literate
import Fren.Trace
import Spec.Language.NamesAndScope
import Spec.Support.Core

open Fren.Lang

#fren_md "Types.md"

set_option warningAsError true in
#fren_check

namespace Spec.Language.Types

open spec.surface spec.names spec.types
open Spec.Language.NamesAndScope (lookup_bound lookup_none)

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
theorem rule_unique (symbols : Snoc Entry) (context : Snoc Ty) (form : CoreF Typing) (a b : Ty)
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
  | Let annotation value body =>
    cases annotation <;> simp [rule?, let_rule?, let_annotated_rule?, fren_spec] at ha hb <;> simp_all
  | _ =>
    simp [rule?, boolean_rule?, integer_rule?, local_rule?, if_rule?,
      fren_spec] at ha hb <;> simp_all

/-- Every local of a valid table is in scope in its row's context. -/
theorem table_scoped (symbols : Snoc Entry) (rows : Snoc Row) (position level : Int) (r : Row)
    (valid : rows_valid? symbols rows = true) (found : lookup _ rows position = some r)
    (form : r.form = .Local level) : 0 ≤ level ∧ level < length _ r.ctx := by
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
      exact ih valid.1.1 found

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
      have heq := ih rearlier hl.1.1 hr.1.1 hrest
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
    (hc : ctx_ok? symbols context = true) (h : lookup _ context level = some ty) :
    ty_ok? symbols ty = true := by
  induction context with
  | Empty => simp [lookup] at h
  | Extend earlier last ih =>
    simp only [ctx_ok?, decide_eq_true_eq] at hc
    simp only [lookup] at h
    split at h
    · have := Option.some.inj h; subst this
      have h1 := hc.1
      cases last <;> simp_all [ty_ok?, fren_spec]
    · exact ih hc.2 h

theorem entry_kind_ok (symbols bindings : Snoc Entry) (item : Fren.Seq String) (kind : ItemKind)
    (hb : bindings_ok? symbols bindings = true) (h : entry bindings item = some kind) :
    (∀ owner, kind = .Constructor owner → ty_ok? symbols (.Nominal owner) = true) ∧
    (∀ signature, kind = .Function signature → ty_ok? symbols signature.result = true) := by
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
        simp only [ty_ok?]
        cases he : entry symbols owner with
        | none => simp [he, fren_spec] at h2
        | some k => cases k <;> simp [he, fren_spec] at h2 ⊢
      · intro signature hk
        simp only at hk; subst hk
        simp [fren_spec] at h2
        have h3 := h2.2
        generalize signature.result = t at h3 ⊢
        cases t <;> simp [ty_ok?, fren_spec] at h3 ⊢
        exact h3
    · exact ih hb.2 h

/-- A constructor's owner, and a function's result, are well formed. -/
theorem entry_types_ok (symbols : Snoc Entry) (item : Fren.Seq String) (hs : symb_ok? symbols = true) :
    (∀ owner, entry symbols item = some (.Constructor owner) → ty_ok? symbols (.Nominal owner) = true) ∧
    (∀ signature, entry symbols item = some (.Function signature) →
      ty_ok? symbols signature.result = true) := by
  have hs' : bindings_ok? symbols symbols = true := by simpa [symb_ok?] using hs
  exact ⟨fun owner h => (entry_kind_ok symbols symbols item _ hs' h).1 owner rfl,
    fun signature h => (entry_kind_ok symbols symbols item _ hs' h).2 signature rfl⟩

theorem typings_ok_extend (symbols : Snoc Entry) (earlier : Snoc Typing) (t : Typing) :
    typings_ok? symbols (.Extend earlier t) = true ↔
      ty_ok? symbols t.ty = true ∧ typings_ok? symbols earlier = true := by
  rcases t with ⟨c, ty⟩
  cases ty <;> simp [typings_ok?, ty_ok?, fren_spec]

/-- One layer: a typed layer over well-formed children has a well-formed type. -/
theorem layer_regular (symbols : Snoc Entry) (context : Snoc Ty) (form : CoreF Typing) (ty : Ty)
    (hs : symb_ok? symbols = true) (hc : ctx_ok? symbols context = true)
    (hch : children_ok? symbols form = true) (h : rule? symbols context form ty = true) :
    ty_ok? symbols ty = true := by
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
      simp [h, ty_ok?, fren_spec]
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
    have hty : body.ty = ty := by
      cases annotation <;> simp [rule?, let_rule?, let_annotated_rule?, fren_spec] at h <;> simp_all
    simp only [children, two, one] at hch
    rw [← hty]
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
    (child : ∀ p t, typing_at rows p = some t → ty_ok? symbols t.ty = true)
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
    (child : ∀ p t, typing_at rows p = some t → ty_ok? symbols t.ty = true)
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
    (ok : ∀ p r, lookup _ rows p = some r → ty_ok? symbols r.ty = true)
    (form : CoreF Int) (typed : CoreF Typing) (h : annotate rows form = some typed) :
    children_ok? symbols typed = true := by
  have child : ∀ p t, typing_at rows p = some t → ty_ok? symbols t.ty = true := by
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

theorem context_ok_extend (symbols : Snoc Entry) (context : Snoc Ty) (t : Ty) :
    ctx_ok? symbols (.Extend context t) = true ↔
      ty_ok? symbols t = true ∧ ctx_ok? symbols context = true := by
  cases t <;> simp [ctx_ok?, ty_ok?, fren_spec]

/-- Over a well-formed environment, every row of a valid table has a
well-formed type. -/
theorem table_regular (symbols : Snoc Entry) (rows : Snoc Row)
    (hs : symb_ok? symbols = true) (hv : rows_valid? symbols rows = true) :
    ∀ p r, lookup _ rows p = some r → ty_ok? symbols r.ty = true := by
  induction rows with
  | Empty => intro p r h; simp [lookup] at h
  | Extend earlier last ih =>
    simp only [rows_valid?, decide_eq_true_eq] at hv
    have ok := ih hv.1.1
    intro p r h
    simp only [lookup] at h
    split at h
    · have := Option.some.inj h; subst this
      have hl := hv.2
      cases ha : annotate earlier last.form with
      | none => simp [ha] at hl
      | some form =>
        simp only [ha] at hl
        exact layer_regular symbols last.ctx form last.ty hs hv.1.2
          (annotate_children_ok symbols earlier ok last.form form ha) hl
    · exact ok p r h

/-- If `derivation?(Σ, rows, Γ, τ)`, then τ is well formed. -/
theorem judgment_regular (symbols : Snoc Entry) (rows : Snoc Row) (context : Snoc Ty) (ty : Ty)
    (h : derivation? symbols rows context ty = true) : ty_ok? symbols ty = true := by
  cases rows with
  | Empty => simp [derivation?, fren_spec] at h
  | Extend earlier root =>
    simp only [derivation?, decide_eq_true_eq] at h
    have hs : symb_ok? symbols = true := by simp only [symb_ok?, decide_eq_true_eq]; exact h.1.1.1.1
    have hroot := h.2
    simp [fren_spec] at hroot
    have := table_regular symbols _ hs h.1.1.2 (length _ earlier) root (by simp [lookup])
    rw [← hroot.2]; exact this

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
theorem layer_weakens (symbols : Snoc Entry) (context : Snoc Ty) (form : CoreF Typing) (ty : Ty)
    (cutoff : Int) (extra : Ty) (h0 : 0 ≤ cutoff) (hn : cutoff ≤ length _ context)
    (h : rule? symbols context form ty = true) :
    rule? symbols (insert_type context cutoff extra) (weaken_layer form cutoff extra) ty = true := by
  cases form with
  | Local level =>
    simp [rule?, local_rule?, fren_spec] at h ⊢
    rw [(lookup_shift context cutoff extra h0 hn).1 level]; exact h
  | Let annotation value body =>
    have he := insert_extend context cutoff extra value.ty hn
    cases annotation <;> simp [rule?, let_rule?, let_annotated_rule?,
      fren_spec] at h ⊢ <;> simp_all
  | Call item args =>
    have hi := in_context_weaken args context cutoff extra
    cases he : entry symbols item with
    | none => simp [rule?, call_rule?, he, fren_spec] at h
    | some kind =>
      cases kind with
      | Function signature =>
        have ha := argument_types_weaken args signature.params cutoff extra
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
  { form := shift_form r.form cutoff, ctx := insert_type r.ctx cutoff extra, ty := r.ty }

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

theorem annotate_weaken (rows : Snoc Row) (cutoff : Int) (extra : Ty) (form : CoreF Int) :
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

theorem context_ok_insert (symbols : Snoc Entry) (context : Snoc Ty) (cutoff : Int) (extra : Ty)
    (hx : ty_ok? symbols extra = true) (hc : ctx_ok? symbols context = true)
    (h0 : 0 ≤ cutoff) (hn : cutoff ≤ length _ context) :
    ctx_ok? symbols (insert_type context cutoff extra) = true := by
  induction context with
  | Empty =>
    simp [length] at hn
    have : cutoff = 0 := by omega
    subst this
    simp only [insert_type]
    exact (context_ok_extend _ _ _).2 ⟨hx, hc⟩
  | Extend earlier t ih =>
    have hc' := (context_ok_extend _ _ _).1 hc
    by_cases e : cutoff = ↑(length _ earlier) + 1
    · simp only [insert_type, if_pos e]
      exact (context_ok_extend _ _ _).2 ⟨hx, hc⟩
    · simp only [length] at hn
      rw [insert_extend earlier cutoff extra t (by push_cast at hn; omega)]
      exact (context_ok_extend _ _ _).2 ⟨hc'.1, ih hc'.2 (by push_cast at hn; omega)⟩

/-- Weakening a valid table whose row contexts reach the cutoff, by a
well-formed type, keeps it valid. -/
theorem table_weakens (symbols : Snoc Entry) (rows : Snoc Row) (cutoff : Int) (extra : Ty)
    (hx : ty_ok? symbols extra = true) (h0 : 0 ≤ cutoff) (hv : rows_valid? symbols rows = true)
    (hr : contexts_reach? rows cutoff = true) :
    rows_valid? symbols (weaken rows cutoff extra) = true := by
  induction rows with
  | Empty => rfl
  | Extend earlier last ih =>
    simp only [rows_valid?, decide_eq_true_eq] at hv
    simp only [contexts_reach?, decide_eq_true_eq] at hr
    simp only [weaken, rows_valid?, decide_eq_true_eq]
    refine ⟨⟨ih hv.1.1 hr.2, context_ok_insert symbols last.ctx cutoff extra hx hv.1.2 h0 hr.1.2⟩, ?_⟩
    have hl := hv.2
    have ha := annotate_weaken earlier cutoff extra last.form
    cases hf : annotate earlier last.form with
    | none => simp [hf] at hl
    | some form =>
      simp only [hf] at hl ha
      simp only [ha, Option.map]
      exact layer_weakens symbols last.ctx form last.ty cutoff extra h0 hr.1.2 hl

theorem insert_at_end (context : Snoc Ty) (extra : Ty) :
    insert_type context (length _ context) extra = .Extend context extra := by
  cases context with
  | Empty => simp [insert_type, length]
  | Extend earlier t => simp [insert_type, length]

theorem extends_length (context base : Snoc Ty) (h : extends? context base = true) :
    length _ base ≤ length _ context := by
  induction context with
  | Empty =>
    simp [extends?, fren_spec] at h
    subst h; simp [length]
  | Extend earlier t ih =>
    simp [extends?, fren_spec] at h
    rcases h with h | h
    · subst h; simp
    · have := ih h; simp [length]; omega

theorem extends_insert (context base : Snoc Ty) (extra : Ty) (h : extends? context base = true) :
    extends? (insert_type context (length _ base) extra) (.Extend base extra) = true := by
  induction context with
  | Empty =>
    simp [extends?, fren_spec] at h
    subst h
    rw [insert_at_end]; simp [extends?, fren_spec]
  | Extend earlier t ih =>
    by_cases e : Snoc.Extend earlier t = base
    · subst e; rw [insert_at_end]; simp [extends?, fren_spec]
    · simp [extends?, fren_spec, e] at h
      have hl := extends_length earlier base h
      rw [insert_extend earlier _ extra t (by exact_mod_cast hl)]
      have := ih h
      simp [extends?, fren_spec, this]

theorem rows_extend_reach (rows : Snoc Row) (base : Snoc Ty) (h : rows_extend? rows base = true) :
    contexts_reach? rows (length _ base) = true := by
  induction rows with
  | Empty => rfl
  | Extend earlier row ih =>
    simp only [rows_extend?, decide_eq_true_eq] at h
    simp only [contexts_reach?, decide_eq_true_eq]
    have := extends_length row.ctx base h.1
    exact ⟨⟨by omega, by exact_mod_cast this⟩, ih h.2⟩

theorem rows_extend_weaken (rows : Snoc Row) (base : Snoc Ty) (extra : Ty)
    (h : rows_extend? rows base = true) :
    rows_extend? (weaken rows (length _ base) extra) (.Extend base extra) = true := by
  induction rows with
  | Empty => rfl
  | Extend earlier row ih =>
    simp only [rows_extend?, decide_eq_true_eq] at h
    simp only [weaken, rows_extend?, decide_eq_true_eq]
    exact ⟨extends_insert row.ctx base extra h.1, ih h.2⟩

/-- Weakening: if `derivation?(Σ, rows, Γ, τ)` and σ is well formed, then
`derivation?(Σ, weaken(rows, |Γ|, σ), (Γ, σ), τ)`. -/
theorem judgment_weakens (symbols : Snoc Entry) (rows : Snoc Row) (context : Snoc Ty) (ty extra : Ty)
    (hx : ty_ok? symbols extra = true) (h : derivation? symbols rows context ty = true) :
    derivation? symbols (weaken rows (length _ context) extra) (.Extend context extra) ty = true := by
  cases rows with
  | Empty => simp [derivation?, fren_spec] at h
  | Extend earlier root =>
    simp only [derivation?, decide_eq_true_eq] at h ⊢
    have hroot := h.2
    simp [fren_spec] at hroot
    have hv := table_weakens symbols (.Extend earlier root) (length _ context) extra hx
      (by omega) h.1.1.2 (rows_extend_reach _ _ h.1.2)
    have he := rows_extend_weaken (.Extend earlier root) context extra h.1.2
    refine ⟨⟨⟨⟨h.1.1.1.1, (context_ok_extend _ _ _).2 ⟨hx, h.1.1.1.2⟩⟩, hv⟩, he⟩, ?_⟩
    simp [weaken, fren_spec, hroot.1, hroot.2, insert_at_end]

/-! ## Adequacy: tables and trees

The chapter defines `Σ; Γ ⊢ e : τ` by tables. This section reads the same
rules as an inductive relation on `Core` expressions, `Typed`, and shows with
`Spec.Tables` that the two agree (`judgment_adequate`). The table laws above
then hold of expressions: regularity (`typed_regular`), uniqueness
(`typed_unique`, `expression_unique`) and weakening (`typed_weakens`). -/

section Adequacy
open Spec.Tables

/-- How `Spec.Tables` reads a row: its form, and its context and type. -/
def rowView : View Row CoreF Typing := ⟨Row.form, fun r => ⟨r.ctx, r.ty⟩⟩

/-- The one-layer rule as a relation on typings: `Σ; Γ ⊢ l ▷ τ`. -/
def Rule (symbols : Snoc Entry) (l : CoreF Typing) (j : Typing) : Prop :=
  rule? symbols j.ctx l j.ty = true

/-- The rule that `rows_valid?` checks of a row: its context is well formed too. -/
def RuleOk (symbols : Snoc Entry) (l : CoreF Typing) (j : Typing) : Prop :=
  ctx_ok? symbols j.ctx = true ∧ Rule symbols l j

/-- The inductive reading of `Σ; Γ ⊢ e : τ`: Σ and Γ are well formed and a
finite tree of instances of the rules concludes it. -/
def Typed (symbols : Snoc Entry) (context : Snoc Ty) (e : Core) (ty : Ty) : Prop :=
  symb_ok? symbols = true ∧ ctx_ok? symbols context = true ∧
    Derives Core.mk (Rule symbols) e ⟨context, ty⟩

theorem annotate_arguments_iff (rows : Snoc Row) (args : Snoc Int) (typed : Snoc Typing) :
    annotate_arguments rows args = some typed ↔
      ∃ zs : Snoc (Int × Typing), mapS Prod.fst zs = args ∧ mapS Prod.snd zs = typed ∧
        ∀ c ∈ toList zs, typing_at rows c.1 = some c.2 := by
  induction args generalizing typed with
  | Empty =>
    constructor
    · intro h
      simp [annotate_arguments] at h
      exact ⟨.Empty, rfl, h, fun _ hc => nomatch hc⟩
    · rintro ⟨zs, h1, h2, -⟩
      cases zs with
      | Empty => simp [annotate_arguments]; exact h2
      | Extend _ _ => simp [mapS] at h1
  | Extend earlier arg ih =>
    constructor
    · intro h
      simp only [annotate_arguments] at h
      cases he : annotate_arguments rows earlier with
      | none => simp [he] at h
      | some te =>
        cases ha : typing_at rows arg with
        | none => simp [he, ha] at h
        | some t =>
          simp [he, ha] at h
          obtain ⟨zs, h1, h2, h3⟩ := (ih te).1 he
          refine ⟨.Extend zs (arg, t), by simp [mapS, h1], by simp [mapS, h2, h], ?_⟩
          intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact ha
          · exact h3 c hc
    · rintro ⟨zs, h1, h2, h3⟩
      cases zs with
      | Empty => simp [mapS] at h1
      | Extend zs z =>
        simp only [mapS, Snoc.Extend.injEq] at h1
        simp only [mapS] at h2
        have he := (ih (mapS Prod.snd zs)).2
          ⟨zs, h1.1, rfl, fun c hc => h3 c (List.mem_cons_of_mem _ hc)⟩
        have ha := h3 z List.mem_cons_self
        rw [h1.2] at ha
        simp only [annotate_arguments, he, ha]
        rw [← h2]

theorem annotate_arms_iff (rows : Snoc Row) (arms : Snoc (ArmF Int)) (typed : Snoc (ArmF Typing)) :
    annotate_arms rows arms = some typed ↔
      ∃ zs : Snoc (ArmF (Int × Typing)), mapS (mapArm Prod.fst) zs = arms ∧
        mapS (mapArm Prod.snd) zs = typed ∧
        ∀ c ∈ toList zs, typing_at rows c.body.1 = some c.body.2 := by
  induction arms generalizing typed with
  | Empty =>
    constructor
    · intro h
      simp [annotate_arms] at h
      exact ⟨.Empty, rfl, h, fun _ hc => nomatch hc⟩
    · rintro ⟨zs, h1, h2, -⟩
      cases zs with
      | Empty => simp [annotate_arms]; exact h2
      | Extend _ _ => simp [mapS] at h1
  | Extend earlier arm ih =>
    constructor
    · intro h
      simp only [annotate_arms] at h
      cases he : annotate_arms rows earlier with
      | none => simp [he] at h
      | some te =>
        cases ha : typing_at rows arm.body with
        | none => simp [he, ha] at h
        | some t =>
          simp [he, ha] at h
          obtain ⟨zs, h1, h2, h3⟩ := (ih te).1 he
          refine ⟨.Extend zs ⟨arm.constructor, (arm.body, t)⟩, by simp [mapS, mapArm, h1],
            by simp [mapS, mapArm, h2, h], ?_⟩
          intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact ha
          · exact h3 c hc
    · rintro ⟨zs, h1, h2, h3⟩
      cases zs with
      | Empty => simp [mapS] at h1
      | Extend zs z =>
        simp only [mapS, Snoc.Extend.injEq] at h1
        simp only [mapS] at h2
        obtain ⟨h1a, rfl⟩ := h1
        have he := (ih (mapS (mapArm Prod.snd) zs)).2
          ⟨zs, h1a, rfl, fun c hc => h3 c (List.mem_cons_of_mem _ hc)⟩
        have ha := h3 z List.mem_cons_self
        simp only [annotate_arms, he, mapArm, ha]
        rw [← h2]; rfl

/-! ### The table check is the generic validity -/

theorem annotate_iff (rows : Snoc Row) (form : CoreF Int) (typed : CoreF Typing) :
    annotate rows form = some typed ↔
      ∃ a : CoreF (Int × Typing), mapF Prod.fst a = form ∧ mapF Prod.snd a = typed ∧
        ∀ c ∈ childrenF a, typing_at rows c.1 = some c.2 := by
  constructor
  · intro h
    cases form with
    | BooleanLiteral b =>
      simp [annotate] at h; exact ⟨.BooleanLiteral b, rfl, h, by simp [childrenF]⟩
    | IntegerLiteral b =>
      simp [annotate] at h; exact ⟨.IntegerLiteral b, rfl, h, by simp [childrenF]⟩
    | Local b => simp [annotate] at h; exact ⟨.Local b, rfl, h, by simp [childrenF]⟩
    | Constructor b =>
      simp [annotate] at h; exact ⟨.Constructor b, rfl, h, by simp [childrenF]⟩
    | Unary op x =>
      cases hx : typing_at rows x with
      | none => simp [annotate, hx] at h
      | some t =>
        simp [annotate, hx] at h
        exact ⟨.Unary op (x, t), rfl, h, by simp [childrenF, hx]⟩
    | Binary op x y =>
      cases hx : typing_at rows x with
      | none => simp [annotate, hx] at h
      | some t =>
        cases hy : typing_at rows y with
        | none => simp [annotate, hx, hy] at h
        | some u =>
          simp [annotate, hx, hy] at h
          exact ⟨.Binary op (x, t) (y, u), rfl, h, by simp [childrenF, hx, hy]⟩
    | Call item args =>
      cases hx : annotate_arguments rows args with
      | none => simp [annotate, hx] at h
      | some ts =>
        simp [annotate, hx] at h
        obtain ⟨zs, h1, h2, h3⟩ := (annotate_arguments_iff rows args ts).1 hx
        exact ⟨.Call item zs, by simp [mapF, h1], by simp [mapF, h2, h], h3⟩
    | Let ann x y =>
      cases hx : typing_at rows x with
      | none => simp [annotate, hx] at h
      | some t =>
        cases hy : typing_at rows y with
        | none => simp [annotate, hx, hy] at h
        | some u =>
          simp [annotate, hx, hy] at h
          exact ⟨.Let ann (x, t) (y, u), rfl, h, by simp [childrenF, hx, hy]⟩
    | If x y z =>
      cases hx : typing_at rows x with
      | none => simp [annotate, hx] at h
      | some t =>
        cases hy : typing_at rows y with
        | none => simp [annotate, hx, hy] at h
        | some u =>
          cases hz : typing_at rows z with
          | none => simp [annotate, hx, hy, hz] at h
          | some v =>
            simp [annotate, hx, hy, hz] at h
            exact ⟨.If (x, t) (y, u) (z, v), rfl, h, by simp [childrenF, hx, hy, hz]⟩
    | Match x arms =>
      cases hx : typing_at rows x with
      | none => simp [annotate, hx] at h
      | some t =>
        cases hy : annotate_arms rows arms with
        | none => simp [annotate, hx, hy] at h
        | some ts =>
          simp [annotate, hx, hy] at h
          obtain ⟨zs, h1, h2, h3⟩ := (annotate_arms_iff rows arms ts).1 hy
          refine ⟨.Match (x, t) zs, by simp [mapF, h1], by simp [mapF, h2, h], ?_⟩
          intro c hc
          simp only [childrenF, List.mem_cons, List.mem_map] at hc
          rcases hc with rfl | ⟨c0, hc0, rfl⟩
          · exact hx
          · exact h3 c0 hc0
  · rintro ⟨a, rfl, rfl, hc⟩
    cases a with
    | BooleanLiteral _ | IntegerLiteral _ | Local _ | Constructor _ => rfl
    | Unary op x =>
      have hx := hc x (by simp [childrenF])
      simp [annotate, mapF, hx]
    | Binary op x y =>
      have hx := hc x (by simp [childrenF])
      have hy := hc y (by simp [childrenF])
      simp [annotate, mapF, hx, hy]
    | Call item zs =>
      have := (annotate_arguments_iff rows _ _).2 ⟨zs, rfl, rfl, hc⟩
      simp [annotate, mapF, this]
    | Let ann x y =>
      have hx := hc x (by simp [childrenF])
      have hy := hc y (by simp [childrenF])
      simp [annotate, mapF, hx, hy]
    | If x y z =>
      have hx := hc x (by simp [childrenF])
      have hy := hc y (by simp [childrenF])
      have hz := hc z (by simp [childrenF])
      simp [annotate, mapF, hx, hy, hz]
    | Match x zs =>
      have hx := hc x (by simp [childrenF])
      have := (annotate_arms_iff rows _ _).2 ⟨zs, rfl, rfl, fun c hc' =>
        hc c.body (by simp only [childrenF]; exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨c, hc', rfl⟩))⟩
      simp [annotate, mapF, hx, this]

theorem typing_at_iff (rows : Snoc Row) (p : Int) (t : Typing) :
    typing_at rows p = some t ↔ ∃ r, lookup Row rows p = some r ∧ rowView.concl r = t := by
  simp only [typing_at, rowView]
  cases lookup Row rows p with
  | none => simp
  | some r => simp

theorem justified_iff (symbols : Snoc Entry) (earlier : Snoc Row) (row : Row) :
    Justified rowView (RuleOk symbols) earlier (length Row earlier) row ↔
      ctx_ok? symbols row.ctx = true ∧
        ∃ typed, annotate earlier row.form = some typed ∧
          rule? symbols row.ctx typed row.ty = true := by
  constructor
  · rintro ⟨a, hf, ⟨hok, hr⟩, hc⟩
    exact ⟨hok, Layer.map Prod.snd a, (annotate_iff _ _ _).2
      ⟨a, hf, rfl, fun c hcm => (typing_at_iff _ _ _).2 (hc c hcm).2⟩, hr⟩
  · rintro ⟨hok, typed, ha, hr⟩
    obtain ⟨a, hf, rfl, hc⟩ := (annotate_iff _ _ _).1 ha
    refine ⟨a, hf, ⟨hok, hr⟩, fun c hcm => ?_⟩
    obtain ⟨r, hl, hcl⟩ := (typing_at_iff _ _ _).1 (hc c hcm)
    exact ⟨lookup_lt hl, r, hl, hcl⟩

/-- `rows_valid?` is validity for the rule. -/
theorem valid_iff (symbols : Snoc Entry) (rows : Snoc Row) :
    rows_valid? symbols rows = true ↔ Valid rowView (RuleOk symbols) rows := by
  induction rows with
  | Empty => simp only [rows_valid?, true_iff]; exact Valid.empty _ _
  | Extend earlier row ih =>
    rw [valid_extend, justified_iff, ← ih]
    simp only [rows_valid?, decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨h.1.1, h.1.2, ?_⟩
      have h2 := h.2
      cases ha : annotate earlier row.form with
      | none => simp [ha] at h2
      | some typed =>
        simp only [ha] at h2
        exact ⟨typed, rfl, of_decide_eq_true h2⟩
    · rintro ⟨h1, h2, typed, ha, hr⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      simp only [ha]; exact decide_eq_true hr

/-! ### The contexts of a rule's premises -/

theorem in_context_mem (args : Snoc Typing) (context : Snoc Ty)
    (h : in_context? args context = true) : ∀ c ∈ toList args, c.ctx = context := by
  induction args with
  | Empty => intro c hc; nomatch hc
  | Extend earlier arg ih =>
    simp only [in_context?, decide_eq_true_eq] at h
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact ih h.2 c hc

theorem arm_bodies_mem (arms : Snoc (ArmF Typing)) (context : Snoc Ty) (ty : Ty)
    (h : arm_bodies? arms context ty = true) : ∀ c ∈ toList arms, c.body.ctx = context := by
  induction arms with
  | Empty => intro c hc; nomatch hc
  | Extend earlier arm ih =>
    simp only [arm_bodies?, decide_eq_true_eq] at h
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1.1
    · exact ih h.2 c hc

/-- The contexts of a rule's premises: a let's body is typed in the context
extended by its value's type, and every other premise in the conclusion's
context. -/
theorem rule_child_ctx (symbols : Snoc Entry) (context : Snoc Ty) (l : CoreF Typing) (ty : Ty)
    (h : rule? symbols context l ty = true) :
    match l with
    | .Let _ value body => value.ctx = context ∧ body.ctx = .Extend context value.ty
    | l => ∀ c ∈ childrenF l, c.ctx = context := by
  cases l with
  | BooleanLiteral _ | IntegerLiteral _ | Local _ | Constructor _ => intro c hc; nomatch hc
  | Unary op x =>
    simp [rule?, unary_rule?, fren_spec] at h
    simp [childrenF, h.1]
  | Binary op x y =>
    simp [rule?, binary_rule?, fren_spec] at h
    simp [childrenF, h.1.1, h.1.2]
  | Call item args =>
    simp only [rule?, call_rule?, decide_eq_true_eq] at h
    split at h
    · exact in_context_mem args context h.1.2
    · nomatch h
  | Let ann x y =>
    cases ann with
    | none => simp [rule?, let_rule?, fren_spec] at h; exact ⟨h.1.1, h.1.2⟩
    | some w =>
      simp [rule?, let_annotated_rule?, let_rule?, fren_spec] at h; exact ⟨h.2.1.1, h.2.1.2⟩
  | If x y z =>
    simp [rule?, if_rule?, fren_spec] at h
    simp [childrenF, h]
  | Match x arms =>
    simp only [rule?, match_rule?, decide_eq_true_eq] at h
    intro c hc
    simp only [childrenF, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨c0, hc0, rfl⟩
    · exact h.1.1.1
    · exact arm_bodies_mem arms context ty h.1.2 c0 hc0

/-! ### Regularity for trees -/

theorem typings_ok_iff (symbols : Snoc Entry) (xs : Snoc Typing) :
    typings_ok? symbols xs = true ↔ ∀ c ∈ toList xs, ty_ok? symbols c.ty = true := by
  induction xs with
  | Empty => simp [typings_ok?, toList]
  | Extend earlier x ih =>
    rw [typings_ok_extend, ih]
    simp only [toList, List.mem_cons]
    constructor
    · rintro ⟨h1, h2⟩ c (rfl | hc)
      · exact h1
      · exact h2 c hc
    · intro h; exact ⟨h x (Or.inl rfl), fun c hc => h c (Or.inr hc)⟩

theorem toList_arm_typings (arms : Snoc (ArmF Typing)) :
    toList (arm_typings arms) = (toList arms).map (·.body) := by
  induction arms with
  | Empty => simp [arm_typings, toList]
  | Extend earlier arm ih => simp [arm_typings, toList, ih]

theorem mem_children_iff (l : CoreF Typing) (c : Typing) :
    c ∈ toList (Fren.Generated.spec.types.children l) ↔ c ∈ childrenF l := by
  cases l <;>
    simp only [Fren.Generated.spec.types.children, childrenF, toList, toList_arm_typings,
      List.mem_cons, List.mem_nil_iff, false_or, List.mem_map, or_comm, or_left_comm]

theorem children_ok_iff (symbols : Snoc Entry) (l : CoreF Typing) :
    children_ok? symbols l = true ↔ ∀ c ∈ childrenF l, ty_ok? symbols c.ty = true := by
  have h : children_ok? symbols l = true
      ↔ typings_ok? symbols (Fren.Generated.spec.types.children l) = true := by
    simp only [children_ok?, decide_eq_true_eq]
  rw [h, typings_ok_iff]
  exact ⟨fun h c hc => h c ((mem_children_iff l c).2 hc),
    fun h c hc => h c ((mem_children_iff l c).1 hc)⟩

/-- Regularity for trees: over a well-formed environment and context, every
node of a derivation has a well-formed context and the conclusion a
well-formed type. -/
theorem derives_regular (symbols : Snoc Entry) (hs : symb_ok? symbols = true) {e : Core}
    {j : Typing} (h : Derives Core.mk (Rule symbols) e j) :
    ctx_ok? symbols j.ctx = true →
      Derives Core.mk (RuleOk symbols) e j ∧ ty_ok? symbols j.ty = true := by
  induction h with
  | node a j _ hra ih =>
    intro hc
    have hctx := rule_child_ctx symbols j.ctx (mapF Prod.snd a) j.ty hra
    have hall : ∀ c ∈ childrenF a, ctx_ok? symbols c.2.ctx = true := by
      cases a with
      | Let ann v b =>
        obtain ⟨hv, hb⟩ : v.2.ctx = j.ctx ∧ b.2.ctx = .Extend j.ctx v.2.ty := hctx
        have hvok : ctx_ok? symbols v.2.ctx = true := by rw [hv]; exact hc
        intro c hcm
        simp only [childrenF, List.mem_cons, List.mem_nil_iff, or_false] at hcm
        rcases hcm with rfl | rfl
        · exact hvok
        · rw [hb, context_ok_extend]
          exact ⟨(ih v (by simp [Layer.children, childrenF]) hvok).2, hc⟩
      | _ =>
        intro c hcm
        have := hctx c.2 (mem_map_of_mem (F := CoreF) Prod.snd hcm)
        rw [this]; exact hc
    have hty : ty_ok? symbols j.ty = true := by
      refine layer_regular symbols j.ctx (mapF Prod.snd a) j.ty hs hc ?_ hra
      rw [children_ok_iff]
      intro c hcm
      rw [show childrenF (mapF Prod.snd a) = (childrenF a).map Prod.snd from
        Layer.children_map (F := CoreF) Prod.snd a] at hcm
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hcm
      exact (ih c0 hc0 (hall c0 hc0)).2
    exact ⟨Derives.node a j (fun c hcm => (ih c hcm (hall c hcm)).1) ⟨hc, hra⟩, hty⟩

/-! ### Adequacy -/

theorem extends_refl (context : Snoc Ty) : extends? context context = true := by
  cases context <;> simp [extends?]

theorem extends_step (context base : Snoc Ty) (t : Ty) (h : extends? context base = true) :
    extends? (.Extend context t) base = true := by
  rw [extends?]; simp [h]

theorem rows_extend_of_lookup (rows : Snoc Row) (base : Snoc Ty)
    (h : ∀ p r, lookup Row rows p = some r → extends? r.ctx base = true) :
    rows_extend? rows base = true := by
  induction rows with
  | Empty => simp [rows_extend?]
  | Extend earlier row ih =>
    simp only [rows_extend?, decide_eq_true_eq]
    refine ⟨h (length Row earlier) row (by rw [lookup_extend, if_pos rfl]), ih ?_⟩
    exact fun p r hl => h p r (Extends.extend earlier row p r hl)

theorem rule_extends (symbols : Snoc Entry) (base : Snoc Ty) (l : CoreF Typing) (j : Typing)
    (h : RuleOk symbols l j) (hq : extends? j.ctx base = true) :
    ∀ c ∈ childrenF l, extends? c.ctx base = true := by
  have hctx := rule_child_ctx symbols j.ctx l j.ty h.2
  cases l with
  | Let ann v b =>
    obtain ⟨hv, hb⟩ : v.ctx = j.ctx ∧ b.ctx = .Extend j.ctx v.ty := hctx
    intro c hcm
    simp only [childrenF, List.mem_cons, List.mem_nil_iff, or_false] at hcm
    rcases hcm with rfl | rfl
    · rw [hv]; exact hq
    · rw [hb]; exact extends_step _ _ _ hq
  | _ => intro c hcm; rw [hctx c hcm]; exact hq

theorem root_position (earlier : Snoc Row) (root : Row) :
    ((length Row (.Extend earlier root) : Nat) : Int) - 1 = length Row earlier := by
  simp only [length]; omega

/-- The expression that a table's root unfolds to. -/
def RootUnfolds (rows : Snoc Row) (e : Core) : Prop :=
  Unfolds rowView Core.mk rows ((length Row rows : Int) - 1) e

/-- Soundness of tables: a derivation's root unfolds to an expression that
the rules type. -/
theorem derivation_typed (symbols : Snoc Entry) (rows : Snoc Row) (context : Snoc Ty) (ty : Ty)
    (h : derivation? symbols rows context ty = true) :
    ∃ e, RootUnfolds rows e ∧ Typed symbols context e ty := by
  cases rows with
  | Empty => simp [derivation?, fren_spec] at h
  | Extend earlier root =>
    simp only [derivation?, decide_eq_true_eq] at h
    have hs : symb_ok? symbols = true := by
      simp only [symb_ok?, decide_eq_true_eq]; exact h.1.1.1.1
    have hroot := h.2
    simp [fren_spec] at hroot
    have hl : lookup Row (.Extend earlier root) (length Row earlier) = some root := by
      rw [lookup_extend, if_pos rfl]
    obtain ⟨t, hut, hdt⟩ := Valid.derives Core.mk ((valid_iff symbols _).1 h.1.1.2) hl
    have hj : rowView.concl root = ⟨context, ty⟩ := by
      rw [← hroot.1, ← hroot.2]; rfl
    rw [hj] at hdt
    refine ⟨t, ?_, hs, h.1.1.1.2, Derives.mono (fun _ _ hr => hr.2) hdt⟩
    unfold RootUnfolds; rw [root_position]; exact hut

/-- Adequacy: the table judgment agrees with the inductive reading of the
rules. Some table is a derivation of `ty` in `context` whose root unfolds to
`e` exactly when Σ and Γ are well formed and a tree of rule instances
concludes it. -/
theorem judgment_adequate (symbols : Snoc Entry) (context : Snoc Ty) (e : Core) (ty : Ty) :
    (∃ rows, derivation? symbols rows context ty = true ∧ RootUnfolds rows e)
      ↔ Typed symbols context e ty := by
  constructor
  · rintro ⟨rows, h, hu⟩
    obtain ⟨t, hut, ht⟩ := derivation_typed symbols rows context ty h
    rw [← Unfolds.unique hut hu]; exact ht
  · rintro ⟨hs, hc, hd⟩
    have h1 := (derives_regular symbols hs hd hc).1
    have h2 := Derives.strengthen (F := CoreF) (fun j : Typing => extends? j.ctx context = true)
      (fun l j hr hq => rule_extends symbols context l j hr hq) h1 (extends_refl context)
    obtain ⟨rows', r, -, hv, hcl, hu⟩ := Derives.table (V := rowView)
      (fun l j => (⟨l, j.ctx, j.ty⟩ : Row)) (fun _ _ => rfl) (fun _ _ => rfl) h2 .Empty
      (Valid.empty _ _)
    refine ⟨.Extend rows' r, ?_, ?_⟩
    · have hcl' : r.ctx = context ∧ r.ty = ty := by
        have := congrArg Typing.ctx hcl; have := congrArg Typing.ty hcl; constructor <;> assumption
      have hvalid : rows_valid? symbols (.Extend rows' r) = true :=
        (valid_iff symbols _).2 (Valid.mono (fun _ _ hr => hr.1) hv)
      have hext : rows_extend? (.Extend rows' r) context = true :=
        rows_extend_of_lookup _ _ (fun p r' hl => Valid.invariant hv hl)
      have hs' : bindings_ok? symbols symbols = true := by
        simpa only [symb_ok?, decide_eq_true_eq] using hs
      simp only [derivation?, decide_eq_true_eq]
      refine ⟨⟨⟨⟨hs', hc⟩, hvalid⟩, hext⟩, ?_⟩
      simp [fren_spec, hcl'.1, hcl'.2]
    · unfold RootUnfolds; rw [root_position]; exact hu

/-! ### Uniqueness -/

theorem rule_deterministic (symbols : Snoc Entry) (z : CoreF (Typing × Typing)) (j j' : Typing)
    (hz : ∀ c ∈ childrenF z, c.1.ctx = c.2.ctx → c.1 = c.2)
    (h : Rule symbols (mapF Prod.fst z) j) (h' : Rule symbols (mapF Prod.snd z) j')
    (hk : j.ctx = j'.ctx) : j = j' := by
  have hctx := rule_child_ctx symbols j.ctx _ j.ty h
  have hctx' := rule_child_ctx symbols j'.ctx _ j'.ty h'
  have hall : ∀ c ∈ childrenF z, c.1 = c.2 := by
    cases z with
    | Let ann v b =>
      obtain ⟨hv, hb⟩ : v.1.ctx = j.ctx ∧ b.1.ctx = .Extend j.ctx v.1.ty := hctx
      obtain ⟨hv', hb'⟩ : v.2.ctx = j'.ctx ∧ b.2.ctx = .Extend j'.ctx v.2.ty := hctx'
      have hvv : v.1 = v.2 := hz v (by simp [childrenF]) (by rw [hv, hv', hk])
      intro c hcm
      simp only [childrenF, List.mem_cons, List.mem_nil_iff, or_false] at hcm
      rcases hcm with rfl | rfl
      · exact hvv
      · exact hz c (by simp [childrenF]) (by rw [hb, hb', hk, hvv])
    | _ =>
      intro c hcm
      refine hz c hcm ?_
      rw [hctx c.1 (mem_map_of_mem (F := CoreF) Prod.fst hcm),
        hctx' c.2 (mem_map_of_mem (F := CoreF) Prod.snd hcm), hk]
  have hform : mapF Prod.fst z = mapF Prod.snd z :=
    Layer.map_congr (F := CoreF) Prod.fst Prod.snd z hall
  unfold Rule at h h'
  rw [hform, hk] at h
  have := rule_unique symbols j'.ctx _ j.ty j'.ty h h'
  obtain ⟨c1, t1⟩ := j; obtain ⟨c2, t2⟩ := j'
  have hk' : c1 = c2 := hk
  have ht : t1 = t2 := this
  rw [hk', ht]

/-- Uniqueness for trees: an expression has at most one type in a context. -/
theorem typed_unique (symbols : Snoc Entry) (context : Snoc Ty) (e : Core) (a b : Ty)
    (ha : Typed symbols context e a) (hb : Typed symbols context e b) : a = b :=
  congrArg Typing.ty (Derives.unique (F := CoreF) (fun _ _ h => Core.mk.inj h) Typing.ctx
    (rule_deterministic symbols) ha.2.2 _ hb.2.2 rfl)

theorem children_paired_zip (pairs : Snoc Pair) (xs : Snoc Int) :
    ∀ ys : Snoc Int, children_paired? pairs xs ys = true →
      ∃ zs : Snoc (Int × Int), mapS Prod.fst zs = xs ∧ mapS Prod.snd zs = ys ∧
        ∀ c ∈ toList zs, paired? pairs c.1 c.2 = true := by
  induction xs with
  | Empty =>
    intro ys h
    cases ys with
    | Empty => exact ⟨.Empty, rfl, rfl, fun _ hc => nomatch hc⟩
    | Extend _ _ => simp [children_paired?] at h
  | Extend e x ih =>
    intro ys h
    cases ys with
    | Empty => simp [children_paired?] at h
    | Extend e' y =>
      simp only [children_paired?, decide_eq_true_eq] at h
      obtain ⟨zs, h1, h2, h3⟩ := ih e' h.2
      refine ⟨.Extend zs (x, y), by simp [mapS, h1], by simp [mapS, h2], ?_⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h.1
      · exact h3 c hc

theorem arms_paired_zip (pairs : Snoc Pair) (xs : Snoc (ArmF Int)) :
    ∀ ys : Snoc (ArmF Int), arms_paired? pairs xs ys = true →
      ∃ zs : Snoc (ArmF (Int × Int)), mapS (mapArm Prod.fst) zs = xs ∧
        mapS (mapArm Prod.snd) zs = ys ∧
        ∀ c ∈ toList zs, paired? pairs c.body.1 c.body.2 = true := by
  induction xs with
  | Empty =>
    intro ys h
    cases ys with
    | Empty => exact ⟨.Empty, rfl, rfl, fun _ hc => nomatch hc⟩
    | Extend _ _ => simp [arms_paired?] at h
  | Extend e x ih =>
    intro ys h
    cases ys with
    | Empty => simp [arms_paired?] at h
    | Extend e' y =>
      simp only [arms_paired?, decide_eq_true_eq] at h
      obtain ⟨zs, h1, h2, h3⟩ := ih e' h.2
      obtain ⟨xc, xb⟩ := x
      obtain ⟨yc, yb⟩ := y
      have hcn : xc = yc := h.1.1
      subst hcn
      refine ⟨.Extend zs ⟨xc, (xb, yb)⟩, by simp [mapS, mapArm, h1], by simp [mapS, mapArm, h2], ?_⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h.1.2
      · exact h3 c hc

/-- Paired layers have one shape: a layer of pairs projects to both. -/
theorem layers_paired_zip (pairs : Snoc Pair) (f g : CoreF Int)
    (h : layers_paired? pairs f g = true) :
    ∃ z : CoreF (Int × Int), mapF Prod.fst z = f ∧ mapF Prod.snd z = g ∧
      ∀ c ∈ childrenF z, paired? pairs c.1 c.2 = true := by
  cases f with
  | BooleanLiteral b =>
    cases g <;> simp [layers_paired?, fren_spec] at h
    subst h; exact ⟨.BooleanLiteral b, rfl, rfl, fun _ hc => nomatch hc⟩
  | IntegerLiteral n =>
    cases g <;> simp [layers_paired?, fren_spec] at h
    subst h; exact ⟨.IntegerLiteral n, rfl, rfl, fun _ hc => nomatch hc⟩
  | Local level =>
    cases g <;> simp [layers_paired?, fren_spec] at h
    subst h; exact ⟨.Local level, rfl, rfl, fun _ hc => nomatch hc⟩
  | Constructor item =>
    cases g <;> simp [layers_paired?, fren_spec] at h
    subst h; exact ⟨.Constructor item, rfl, rfl, fun _ hc => nomatch hc⟩
  | Unary op x =>
    cases g <;> simp [layers_paired?, fren_spec] at h
    rename_i op' y
    obtain ⟨rfl, hp⟩ := h
    exact ⟨.Unary op (x, y), rfl, rfl, by simpa [childrenF] using hp⟩
  | Binary op x1 x2 =>
    cases g <;> simp [layers_paired?, fren_spec] at h
    rename_i op' y1 y2
    obtain ⟨⟨rfl, hp1⟩, hp2⟩ := h
    exact ⟨.Binary op (x1, y1) (x2, y2), rfl, rfl, by simp [childrenF, hp1, hp2]⟩
  | Call item xs =>
    cases g <;> simp [layers_paired?, fren_spec] at h
    rename_i item' ys
    obtain ⟨rfl, hp⟩ := h
    obtain ⟨zs, h1, h2, h3⟩ := children_paired_zip pairs xs ys hp
    exact ⟨.Call item zs, by simp [mapF, h1], by simp [mapF, h2], h3⟩
  | Let ann x1 x2 =>
    cases g <;> simp [layers_paired?, fren_spec] at h
    rename_i ann' y1 y2
    obtain ⟨⟨rfl, hp1⟩, hp2⟩ := h
    exact ⟨.Let ann (x1, y1) (x2, y2), rfl, rfl, by simp [childrenF, hp1, hp2]⟩
  | If x1 x2 x3 =>
    cases g <;> simp [layers_paired?, fren_spec] at h
    rename_i y1 y2 y3
    obtain ⟨⟨hp1, hp2⟩, hp3⟩ := h
    exact ⟨.If (x1, y1) (x2, y2) (x3, y3), rfl, rfl, by simp [childrenF, hp1, hp2, hp3]⟩
  | Match x xs =>
    cases g <;> simp [layers_paired?, fren_spec] at h
    rename_i y ys
    obtain ⟨hp, hps⟩ := h
    obtain ⟨zs, h1, h2, h3⟩ := arms_paired_zip pairs xs ys hps
    refine ⟨.Match (x, y) zs, by simp [mapF, h1], by simp [mapF, h2], ?_⟩
    intro c hc
    simp only [childrenF, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨c0, hc0, rfl⟩
    · exact hp
    · exact h3 c0 hc0

theorem pairs_agree_lookup (left right : Snoc Row) (pairs remaining : Snoc Pair)
    (h : pairs_agree? left right pairs remaining = true) :
    ∀ p q, paired? remaining p q = true → ∀ l r, lookup Row left p = some l →
      lookup Row right q = some r → layers_paired? pairs l.form r.form = true := by
  induction remaining with
  | Empty => intro p q hp; simp [paired?] at hp
  | Extend earlier pair ih =>
    intro p q hp l r hl hr
    simp only [pairs_agree?, decide_eq_true_eq] at h
    simp only [paired?, decide_eq_true_eq] at hp
    rcases hp with ⟨rfl, rfl⟩ | hp
    · have h1 := h.1
      rw [hl, hr] at h1
      exact h1
    · exact ih h.2 p q hp l r hl hr

/-- A set of pairs that `pairs_agree?` accepts is a bisimulation. -/
theorem alike_bisim (left right : Snoc Row) (pairs : Snoc Pair)
    (h : pairs_agree? left right pairs pairs = true) :
    Bisim rowView rowView left right (fun p q => paired? pairs p q = true) := by
  intro p q r r' hp hl hr
  exact layers_paired_zip pairs r.form r'.form
    (pairs_agree_lookup left right pairs pairs h p q hp r r' hl hr)

/-- Rows that unfold alike unfold to the same expression. -/
theorem alike_unfolds (left right : Snoc Row) (pairs : Snoc Pair) (p q : Int) (e e' : Core)
    (h : alike? left p right q pairs = true) (hu : Unfolds rowView Core.mk left p e)
    (hu' : Unfolds rowView Core.mk right q e') : e = e' := by
  simp only [alike?, decide_eq_true_eq] at h
  exact Unfolds.alike (alike_bisim left right pairs h.2) hu q e' h.1 hu'

/-- Uniqueness for expressions: two derivations in one context whose roots
unfold alike have the same type. -/
theorem expression_unique (symbols : Snoc Entry) (context : Snoc Ty) (left right : Snoc Row)
    (pairs : Snoc Pair) (a b : Ty) (hl : derivation? symbols left context a = true)
    (hr : derivation? symbols right context b = true)
    (h : alike? left ((length Row left : Int) - 1) right ((length Row right : Int) - 1) pairs
      = true) : a = b := by
  obtain ⟨e, hu, ht⟩ := derivation_typed symbols left context a hl
  obtain ⟨e', hu', ht'⟩ := derivation_typed symbols right context b hr
  rw [← alike_unfolds left right pairs _ _ e e' h hu hu'] at ht'
  exact typed_unique symbols context e a b ht ht'

/-- Regularity for expressions: a typed expression has a well-formed type. -/
theorem typed_regular (symbols : Snoc Entry) (context : Snoc Ty) (e : Core) (ty : Ty)
    (h : Typed symbols context e ty) : ty_ok? symbols ty = true :=
  (derives_regular symbols h.1 h.2.2 h.2.1).2

/-! ### Weakening for expressions -/

/-- `e'` is `e` with every local level of at least `cutoff` shifted by one. -/
def Shifted (cutoff : Int) (e e' : Core) : Prop := Mapped (shiftF cutoff) Core.mk e e'

/-- Weakening for expressions: a typed expression, its outer locals shifted
past a new context entry, has the same type in the extended context. -/
theorem typed_weakens (symbols : Snoc Entry) (context : Snoc Ty) (e : Core) (ty extra : Ty)
    (hx : ty_ok? symbols extra = true) (h : Typed symbols context e ty) :
    ∃ e', Shifted (length Ty context) e e' ∧ Typed symbols (.Extend context extra) e' ty := by
  obtain ⟨rows, hd, hu⟩ := (judgment_adequate symbols context e ty).2 h
  have hd' := judgment_weakens symbols rows context ty extra hx hd
  obtain ⟨e', hu', hm⟩ := Unfolds.mapped (V := rowView) (V' := rowView) (con := Core.mk)
    (shiftF (length Ty context)) (shiftF_natural _) (shiftF_within _)
    (rows' := weaken rows (length Ty context) extra)
    (fun p r hl => ⟨weakenRow (length Ty context) extra r, by rw [lookup_weaken, hl]; rfl,
      (shiftF_form _ _).symm⟩) hu
  refine ⟨e', hm, (judgment_adequate symbols _ e' ty).1 ⟨_, hd', ?_⟩⟩
  unfold RootUnfolds
  rw [length_weaken]
  exact hu'

end Adequacy

/-! ## Examples -/

/-- Snoc sequences of one to four entries, oldest first. -/
abbrev t1 {α : Type} (a : α) : Snoc α := .Extend .Empty a
abbrev t2 {α : Type} (a b : α) : Snoc α := .Extend (t1 a) b
abbrev t3 {α : Type} (a b c : α) : Snoc α := .Extend (t2 a b) c
abbrev t4 {α : Type} (a b c d : α) : Snoc α := .Extend (t3 a b c) d

/-- Typed in the empty context at `ty` against the example environment. -/
abbrev typed (rows : Snoc Row) (ty : Ty) : Bool := derivation? SYMB rows .Empty ty

abbrev int (n : Int) : Row := row (.IntegerLiteral n) .Empty .Integer
abbrev bool (b : Bool) : Row := row (.BooleanLiteral b) .Empty .Boolean
abbrev red : Row := row (.Constructor LIGHT_RED) .Empty (.Nominal LIGHT)
abbrev arm (c : Fren.Seq String) (body : Int) : ArmF Int := ⟨c, body⟩

-- A table for ⊢ 7 : Int is valid; one typing 7 at Bool is rejected.
example : typed (t1 (int 7)) .Integer = true := by decide
example : typed (t1 (row (.IntegerLiteral 7) .Empty .Boolean)) .Boolean = false := by decide
-- A table for ⊢ true : Bool is valid.
example : typed (t1 (bool true)) .Boolean = true := by decide
-- This table, for · ⊢ #0, is rejected: level 0 has no entry.
example : typed (t1 (row (.Local 0) .Empty .Integer)) .Integer = false := by decide
-- A table for ·, Bool, Int ⊢ #1 : Int is valid.
example : derivation? SYMB (t1 (row (.Local 1) BOOLEAN_INTEGER .Integer))
    BOOLEAN_INTEGER .Integer = true := by decide
-- A table for ⊢ -1 : Int is valid; one for -true at Int is rejected.
example : typed (t2 (int 1) (row (.Unary .Neg 0) .Empty .Integer)) .Integer = true := by decide
example : typed (t2 (bool true) (row (.Unary .Neg 0) .Empty .Integer)) .Integer = false := by decide
-- A table for ⊢ not true : Bool is valid.
example : typed (t2 (bool true) (row (.Unary .Not 0) .Empty .Boolean)) .Boolean = true := by decide
-- This table is rejected: its child row does not exist.
example : typed (t1 (row (.Unary .Neg 0) .Empty .Integer)) .Integer = false := by decide
-- A table for ⊢ 1 + 2 : Int is valid; one for false + 2 is rejected.
example : typed (t3 (int 1) (int 2) (row (.Binary .Add 0 1) .Empty .Integer)) .Integer = true := by
  decide
example : typed (t3 (bool false) (int 2) (row (.Binary .Add 0 1) .Empty .Integer)) .Integer =
    false := by decide
-- A table for ⊢ 1 < 2 : Bool is valid.
example : typed (t3 (int 1) (int 2) (row (.Binary .Lt 0 1) .Empty .Boolean)) .Boolean = true := by
  decide
-- This table for false and #0 is rejected: its right operand is checked although the left is false.
example : typed (t3 (bool false) (row (.Local 0) .Empty .Boolean)
    (row (.Binary .And 0 1) .Empty .Boolean)) .Boolean = false := by decide
-- A table for ⊢ M::Light::Red = M::Light::Red : Bool is valid; one comparing across enumerations is rejected.
example : typed (t3 red red (row (.Binary .Eq 0 1) .Empty .Boolean)) .Boolean = true := by decide
example : typed (t3 red (row (.Constructor SIGNAL_RED) .Empty (.Nominal SIGNAL))
    (row (.Binary .Eq 0 1) .Empty .Boolean)) .Boolean = false := by decide
-- A table for ⊢ let x := 1 in x : Int is valid; the same table with annotation Bool is rejected.
example : typed (t3 (int 1) (row (.Local 0) (.Extend .Empty .Integer) .Integer)
    (row (.Let none 0 1) .Empty .Integer)) .Integer = true := by decide
example : typed (t3 (int 1) (row (.Local 0) (.Extend .Empty .Integer) .Integer)
    (row (.Let (some .Boolean) 0 1) .Empty .Integer)) .Integer = false := by decide
-- A table for ·, Bool ⊢ let x := 1 in x : Int is valid: its binder has level 1.
example : derivation? SYMB
    (t3 (row (.IntegerLiteral 1) (.Extend .Empty .Boolean) .Integer)
      (row (.Local 1) BOOLEAN_INTEGER .Integer)
      (row (.Let none 0 1) (.Extend .Empty .Boolean) .Integer))
    (.Extend .Empty .Boolean) .Integer = true := by decide
-- A table for ⊢ if true then 1 else 2 : Int is valid; one for if 0 then 1 else 2 is rejected.
example : typed (t4 (bool true) (int 1) (int 2) (row (.If 0 1 2) .Empty .Integer))
    .Integer = true := by decide
example : typed (t4 (int 0) (int 1) (int 2) (row (.If 0 1 2) .Empty .Integer))
    .Integer = false := by decide
-- This table, a match with no arms, is rejected.
example : typed (t2 red (row (.Match 0 .Empty) .Empty .Integer)) .Integer = false := by decide
-- This table, with one arm body of the wrong type, is rejected.
example : typed (t4 red (int 1) (bool true)
    (row (.Match 0 (.Extend (.Extend .Empty (arm LIGHT_RED 1)) (arm LIGHT_GREEN 2))) .Empty .Integer))
    .Integer = false := by decide
-- This table, for M::f(true), is rejected.
example : typed (t2 (bool true) (row (.Call F (.Extend .Empty 0)) .Empty .Integer)) .Integer =
    false := by decide
-- These tables, calling a constructor and using a function as a value, are rejected.
example : typed (t2 (int 1) (row (.Call LIGHT_RED (.Extend .Empty 0)) .Empty .Integer)) .Integer =
    false := by decide
example : typed (t1 (row (.Constructor F) .Empty .Integer)) .Integer = false := by decide
-- This table, typing a constructor at Int, is rejected.
example : typed (t1 (row (.Constructor LIGHT_RED) .Empty .Integer)) .Integer = false := by decide
-- This environment, which binds M::f twice, is ill formed.
example : symb_ok? (.Extend SYMB (bind F (.Constructor LIGHT))) = false := by decide
-- This environment, whose constructor's owner is unbound, is ill formed.
example : symb_ok? (.Extend .Empty (bind LIGHT_RED (.Constructor LIGHT))) = false := by decide
-- Instances of the `?` suffix rule.
example : parameter_type? none true .Boolean = true := by decide
example : parameter_type? none false .Boolean = false := by decide
example : parameter_type? (some .Integer) true .Integer = false := by decide
example : let_annotation? none true (some .Boolean) = true := by decide

-- These programs give M::f no body, two bodies and one body; only the last is well typed.
example : prog_ok? SYMB .Empty = false := by decide
example : prog_ok? SYMB (.Extend (.Extend .Empty
    (.Function F (t1 (row (.Local 0) (.Extend .Empty .Integer) .Integer))))
    (.Function F (t1 (row (.Local 0) (.Extend .Empty .Integer) .Integer)))) = false := by decide
example : prog_ok? SYMB (.Extend .Empty
    (.Function F (t1 (row (.Local 0) (.Extend .Empty .Integer) .Integer)))) = true := by decide

-- These tables are rejected: their environment, or their context, is ill formed.
example : derivation? (.Extend .Empty (bind LIGHT_RED (.Constructor LIGHT))) (t1 (int 7))
    .Empty .Integer = false := by decide
example : derivation? SYMB (t1 (row (.Local 0) (t1 (.Nominal LIGHT_RED)) (.Nominal LIGHT_RED)))
    (t1 (.Nominal LIGHT_RED)) (.Nominal LIGHT_RED) = false := by decide

end Spec.Language.Types

/-! ## Laws bound to their procedures -/

pub mod spec::types

open spec.surface spec.names spec.types in
impl call_arity_proof: call_arity for (args : Snoc Typing) (params : Snoc Ty) {
  args := args, params := params, holds? := true
} by
  intro args params _
  simp only [call_arity.ensures, call_arity.ensure.output, call_arity.ensure.equal]
  refine ⟨trivial, ?_⟩
  intro h
  rw [Spec.Language.Types.argument_types_length args params h]

open spec.surface spec.names spec.types in
impl layer_regularity_proof: layer_regularity for (symb : Snoc Entry) (ctx : Snoc Ty)
    (form : CoreF Typing) (ty : Ty) {
  symb := symb, ctx := ctx, form := form, ty := ty, holds? := true
} by
  intro symb ctx form ty _
  simp only [layer_regularity.ensures, layer_regularity.ensure.output, layer_regularity.ensure.regular]
  refine ⟨trivial, ?_⟩
  intro h
  exact Spec.Language.Types.layer_regular symb ctx form ty h.1.1.1 h.1.1.2 h.1.2 h.2

open spec.surface spec.names spec.types in
impl table_regularity_proof: table_regularity for (symb : Snoc Entry) (rows : Snoc Row)
    (pos : Int) (found : Row) {
  symb := symb, rows := rows, pos := pos, found := found, holds? := true
} by
  intro symb rows pos found _
  simp only [table_regularity.ensures, table_regularity.ensure.output, table_regularity.ensure.regular]
  refine ⟨trivial, ?_⟩
  intro h
  exact Spec.Language.Types.table_regular symb rows h.1.1 h.1.2 pos found h.2

open spec.surface spec.names spec.types in
impl judgment_regularity_proof: judgment_regularity for (symb : Snoc Entry)
    (rows : Snoc Row) (ctx : Snoc Ty) (ty : Ty) {
  symb := symb, rows := rows, ctx := ctx, ty := ty, holds? := true
} by
  intro symb rows ctx ty _
  simp only [judgment_regularity.ensures, judgment_regularity.ensure.output, judgment_regularity.ensure.regular]
  refine ⟨trivial, ?_⟩
  exact Spec.Language.Types.judgment_regular symb rows ctx ty

open spec.surface spec.names spec.types in
impl table_scoping_proof: table_scoping for (symb : Snoc Entry) (rows : Snoc Row)
    (pos : Int) (found : Row) (level : Int) {
  symb := symb, rows := rows, pos := pos, found := found, level := level, holds? := true
} by
  intro symb rows pos found level _
  simp only [spec.types.table_scoping.ensures, spec.types.table_scoping.ensure.output, spec.types.table_scoping.ensure.in_scope]
  refine ⟨trivial, ?_⟩
  intro h
  exact Spec.Language.Types.table_scoped symb rows pos level found h.1.1 h.1.2 h.2

open spec.surface spec.names spec.types in
impl table_uniqueness_proof: table_uniqueness for (symb : Snoc Entry)
    (left right : Snoc Row) {
  symb := symb, left := left, right := right, holds? := true
} by
  intro symb left right _
  simp only [table_uniqueness.ensures, table_uniqueness.ensure.output, table_uniqueness.ensure.equal]
  refine ⟨trivial, ?_⟩
  intro h
  exact Spec.Language.Types.table_unique symb left right h.1.1 h.1.2 h.2

open spec.surface spec.names spec.types in
impl layer_weakening_proof: layer_weakening for (symb : Snoc Entry) (ctx : Snoc Ty)
    (form : CoreF Typing) (ty : Ty) (cutoff : Int) (extra : Ty) {
  symb := symb, ctx := ctx, form := form, ty := ty, cutoff := cutoff, extra := extra, holds? := true
} by
  intro symb ctx form ty cutoff extra _
  simp only [spec.types.layer_weakening.ensures, spec.types.layer_weakening.ensure.output, spec.types.layer_weakening.ensure.weakened]
  refine ⟨trivial, ?_⟩
  intro h
  exact Spec.Language.Types.layer_weakens symb ctx form ty cutoff extra h.1.1 h.1.2 h.2

open spec.surface spec.names spec.types in
impl lookup_shifting_proof: lookup_shifting for (ctx : Snoc Ty) (cutoff : Int)
    (extra : Ty) (level : Int) {
  ctx := ctx, cutoff := cutoff, extra := extra, level := level, holds? := true
} by
  intro ctx cutoff extra level _
  simp only [lookup_shifting.ensures, lookup_shifting.ensure.output, lookup_shifting.ensure.shifted, lookup_shifting.ensure.inserted]
  refine ⟨trivial, ?_⟩
  exact ⟨fun h => (Spec.Language.Types.lookup_shift ctx cutoff extra h.1 h.2).1 level,
    fun h => (Spec.Language.Types.lookup_shift ctx cutoff extra h.1 h.2).2⟩

open spec.surface spec.names spec.types in
impl table_weakening_proof: table_weakening for (symb : Snoc Entry) (rows : Snoc Row)
    (cutoff : Int) (extra : Ty) {
  symb := symb, rows := rows, cutoff := cutoff, extra := extra, holds? := true
} by
  intro symb rows cutoff extra _
  simp only [spec.types.table_weakening.ensures, spec.types.table_weakening.ensure.output, spec.types.table_weakening.ensure.valid]
  refine ⟨trivial, ?_⟩
  intro h
  exact Spec.Language.Types.table_weakens symb rows cutoff extra h.1.1.1 h.1.1.2 h.1.2 h.2

open spec.surface spec.names spec.types in
impl judgment_weakening_proof: judgment_weakening for (symb : Snoc Entry)
    (rows : Snoc Row) (ctx : Snoc Ty) (ty extra : Ty) {
  symb := symb, rows := rows, ctx := ctx, ty := ty, extra := extra, holds? := true
} by
  intro symb rows ctx ty extra _
  simp only [judgment_weakening.ensures, judgment_weakening.ensure.output, judgment_weakening.ensure.weakened]
  refine ⟨trivial, ?_⟩
  intro h
  exact Spec.Language.Types.judgment_weakens symb rows ctx ty extra h.1 h.2

open spec.surface spec.names spec.types in
impl expression_uniqueness_proof: expression_uniqueness for (symb : Snoc Entry) (ctx : Snoc Ty)
    (left right : Snoc Row) (pairs : Snoc Pair) (a b : Ty) {
  symb := symb, ctx := ctx, left := left, right := right, pairs := pairs, a := a, b := b,
  holds? := true
} by
  intro symb ctx left right pairs a b _
  simp only [expression_uniqueness.ensures, expression_uniqueness.ensure.output,
    expression_uniqueness.ensure.unique]
  refine ⟨trivial, ?_⟩
  intro h
  exact Spec.Language.Types.expression_unique symb ctx left right pairs a b h.1.1 h.1.2 h.2

open spec.surface spec.names spec.types in
impl worked_examples_proof: worked_examples { holds? := true } by
  intro _
  simp only [spec.types.worked_examples.ensures, spec.types.worked_examples.ensure.output, spec.types.worked_examples.ensure.valid]
  refine ⟨trivial, ?_⟩
  decide

/-! ## The overview's interface, interpreted by the detailed definitions -/

pub mod spec::typing

interp type_of := fun _ _ rows => match rows with
  | .Empty => default
  | .Extend _ root => root.ty
interp derives? := fun symb ctx rows ty => spec.types.derivation? symb rows ctx ty by
  intro symb ctx rows ty
  simp only [spec.typing.derives?.records_type, spec.typing.derives?.well_formed,
    spec.typing.derives?.regular, spec.typing.type_of]
  refine ⟨fun h => ?_, fun h => ?_, fun h => Spec.Language.Types.judgment_regular symb rows ctx ty h⟩
  · cases rows with
    | Empty => simp [spec.types.derivation?, fren_spec] at h
    | Extend earlier root =>
      simp only [spec.types.derivation?, decide_eq_true_eq] at h
      have hr := h.2
      simp [fren_spec] at hr
      simp [hr.2]
  · simp only [spec.types.derivation?, decide_eq_true_eq] at h
    exact ⟨by simp only [spec.names.symb_ok?, decide_eq_true_eq]; exact h.1.1.1.1, h.1.1.1.2⟩

set_option fren.requireEvidence "trusted" in
#fren_trace
