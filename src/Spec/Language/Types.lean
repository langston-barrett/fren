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

/-! ## Examples -/

/-- The chapter's worked derivations. -/
theorem worked_examples :
    WELL_FORMED_EXAMPLE = true ∧ OLDEST_LEVEL_EXAMPLE = true ∧ LET_EXAMPLE = true ∧
    LET_VALUE_SCOPE_EXAMPLE = true ∧ BOTH_BRANCHES_EXAMPLE = true ∧ MATCH_EXAMPLE = true ∧
    MATCH_OWNER_EXAMPLE = true ∧ CALL_EXAMPLE = true ∧ CONTEXT_ALIGNMENT_EXAMPLE = true ∧
    PROGRAM_EXAMPLE = true := by
  decide

/-- One table: a single row. -/
abbrev one (r : Row) : Snoc Row := .Extend .Empty r
/-- Two, three and four rows, oldest first. -/
abbrev two (a b : Row) : Snoc Row := .Extend (one a) b
abbrev three (a b c : Row) : Snoc Row := .Extend (two a b) c
abbrev four (a b c d : Row) : Snoc Row := .Extend (three a b c) d

/-- Typed in the empty context at `ty` against the example environment. -/
abbrev typed (rows : Snoc Row) (ty : Ty) : Bool := derivation? EXAMPLE_SYMBOLS rows .Empty ty

abbrev int (n : Int) : Row := row (.IntegerLiteral n) .Empty .Integer
abbrev bool (b : Bool) : Row := row (.BooleanLiteral b) .Empty .Boolean
abbrev red : Row := row (.Constructor LIGHT_RED) .Empty (.Nominal LIGHT)
abbrev arm (c : Fren.Seq String) (body : Int) : ArmF Int := ⟨c, body⟩

-- ⊢ 7 : Integer, and not at Boolean.
example : typed (one (int 7)) .Integer = true := by decide
example : typed (one (row (.IntegerLiteral 7) .Empty .Boolean)) .Boolean = false := by decide
-- ⊢ true : Boolean.
example : typed (one (bool true)) .Boolean = true := by decide
-- Rejected: · ⊢ #0, which has no entry.
example : typed (one (row (.Local 0) .Empty .Integer)) .Integer = false := by decide
-- ·, Boolean, Integer ⊢ #1 : Integer.
example : derivation? EXAMPLE_SYMBOLS (one (row (.Local 1) BOOLEAN_INTEGER .Integer))
    BOOLEAN_INTEGER .Integer = true := by decide
-- ⊢ -1 : Integer, and rejected: -true.
example : typed (two (int 1) (row (.Unary .Neg 0) .Empty .Integer)) .Integer = true := by decide
example : typed (two (bool true) (row (.Unary .Neg 0) .Empty .Integer)) .Integer = false := by decide
-- ⊢ not true : Boolean.
example : typed (two (bool true) (row (.Unary .Not 0) .Empty .Boolean)) .Boolean = true := by decide
-- Rejected: a child row that does not exist.
example : typed (one (row (.Unary .Neg 0) .Empty .Integer)) .Integer = false := by decide
-- ⊢ 1 + 2 : Integer; rejected: false + 2.
example : typed (three (int 1) (int 2) (row (.Binary .Add 0 1) .Empty .Integer)) .Integer = true := by
  decide
example : typed (three (bool false) (int 2) (row (.Binary .Add 0 1) .Empty .Integer)) .Integer =
    false := by decide
-- ⊢ 1 < 2 : Boolean.
example : typed (three (int 1) (int 2) (row (.Binary .Lt 0 1) .Empty .Boolean)) .Boolean = true := by
  decide
-- Rejected: the right operand of `and` is checked even when the left is false.
example : typed (three (bool false) (row (.Local 0) .Empty .Boolean)
    (row (.Binary .And 0 1) .Empty .Boolean)) .Boolean = false := by decide
-- ⊢ M::Light::Red = M::Light::Red : Boolean; rejected across enumerations.
example : typed (three red red (row (.Binary .Eq 0 1) .Empty .Boolean)) .Boolean = true := by decide
example : typed (three red (row (.Constructor SIGNAL_RED) .Empty (.Nominal SIGNAL))
    (row (.Binary .Eq 0 1) .Empty .Boolean)) .Boolean = false := by decide
-- ⊢ let 1 in #0 : Integer, without an annotation; rejected with annotation Boolean.
example : typed (three (int 1) (row (.Local 0) (.Extend .Empty .Integer) .Integer)
    (row (.Let none 0 1) .Empty .Integer)) .Integer = true := by decide
example : typed (three (int 1) (row (.Local 0) (.Extend .Empty .Integer) .Integer)
    (row (.Let (some .Boolean) 0 1) .Empty .Integer)) .Integer = false := by decide
-- ·, Boolean ⊢ let 1 in #1 : Integer: the binder has level |Γ| = 1.
example : derivation? EXAMPLE_SYMBOLS
    (three (row (.IntegerLiteral 1) (.Extend .Empty .Boolean) .Integer)
      (row (.Local 1) BOOLEAN_INTEGER .Integer)
      (row (.Let none 0 1) (.Extend .Empty .Boolean) .Integer))
    (.Extend .Empty .Boolean) .Integer = true := by decide
-- ⊢ if true then 1 else 2 : Integer; rejected: if 0 then 1 else 2.
example : typed (four (bool true) (int 1) (int 2) (row (.Conditional 0 1 2) .Empty .Integer))
    .Integer = true := by decide
example : typed (four (int 0) (int 1) (int 2) (row (.Conditional 0 1 2) .Empty .Integer))
    .Integer = false := by decide
-- Rejected: a match with no arms.
example : typed (two red (row (.Match 0 .Empty) .Empty .Integer)) .Integer = false := by decide
-- Rejected: one arm body of the wrong type.
example : typed (four red (int 1) (bool true)
    (row (.Match 0 (.Extend (.Extend .Empty (arm LIGHT_RED 1)) (arm LIGHT_GREEN 2))) .Empty .Integer))
    .Integer = false := by decide
-- Coverage is separate: a partial match and a repeated arm are typed.
example : typed (three red (int 1) (row (.Match 0 (.Extend .Empty (arm LIGHT_RED 1))) .Empty .Integer))
    .Integer = true := by decide
example : typed (three red (int 1)
    (row (.Match 0 (.Extend (.Extend .Empty (arm LIGHT_RED 1)) (arm LIGHT_RED 1))) .Empty .Integer))
    .Integer = true := by decide
-- Rejected: an argument of the wrong type, M::f(true).
example : typed (two (bool true) (row (.Call F (.Extend .Empty 0)) .Empty .Integer)) .Integer =
    false := by decide
-- Rejected: a constructor is not callable, and a function is not a value.
example : typed (two (int 1) (row (.Call LIGHT_RED (.Extend .Empty 0)) .Empty .Integer)) .Integer =
    false := by decide
example : typed (one (row (.Constructor F) .Empty .Integer)) .Integer = false := by decide
-- Rejected: a constructor typed at another type than its owner.
example : typed (one (row (.Constructor LIGHT_RED) .Empty .Integer)) .Integer = false := by decide
-- A duplicate binding makes an environment ill formed.
example : symbols_ok? (.Extend EXAMPLE_SYMBOLS (binding F (.Constructor LIGHT))) = false := by decide
-- A constructor's owner must list it.
example : symbols_ok? (.Extend .Empty (binding LIGHT_RED (.Constructor LIGHT))) = false := by decide
-- The `?` suffix rule.
example : parameter_type? none true .Boolean = true := by decide
example : parameter_type? none false .Boolean = false := by decide
example : parameter_type? (some .Integer) true .Integer = false := by decide
example : let_annotation? none true (some .Boolean) = true := by decide
-- Value ownership and direct mentions.
example : value_valid? EXAMPLE_SYMBOLS (.Nominal LIGHT LIGHT_RED) = true := by decide
example : value_valid? EXAMPLE_SYMBOLS (.Nominal SIGNAL LIGHT_RED) = false := by decide
example : direct_item? (.Call F .Empty) F = true := by decide

-- A program needs exactly one body for each function: none and two are rejected.
example : program_ok? EXAMPLE_SYMBOLS .Empty = false := by decide
example : program_ok? EXAMPLE_SYMBOLS (.Extend (.Extend .Empty
    (.Function F (one (row (.Local 0) (.Extend .Empty .Integer) .Integer))))
    (.Function F (one (row (.Local 0) (.Extend .Empty .Integer) .Integer)))) = false := by decide
example : program_ok? EXAMPLE_SYMBOLS (.Extend .Empty
    (.Function F (one (row (.Local 0) (.Extend .Empty .Integer) .Integer)))) = true := by decide

end Spec.Language.Types
