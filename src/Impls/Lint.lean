-- keep-sorted start
import Impls.Lang
import Impls.View
-- keep-sorted end
open Fren.Lang

/-! # Lints (`Reqs/Lint`) -/

namespace Fren.Impls

open Fren.Core (LintLevel Case Named ImportFix setLevel effectiveLevel unusedImport inCase
  expectationFulfilled expectationReported importFix fixExit fixSelected Comparison deadItem literalNegated)

instance : Fren.Finite LintLevel :=
  ⟨[.allow, .expect, .warn, .deny, .forbid], by intro x; cases x <;> simp⟩

instance : Fren.Finite Case := ⟨[.snake, .camel, .upper], by intro x; cases x <;> simp⟩

instance : Fren.Finite Named :=
  ⟨[.module, .component, .variable, .field, .binder, .function, .instance, .constraint, .global, .enumeration,
    .variant, .record, .abstractType, .constant],
    by intro x; cases x <;> simp⟩

instance : Fren.Finite Comparison := ⟨Comparison.all.toList, by intro x; cases x <;> simp [Comparison.all]⟩

def toComparison : Comparison → lint.Comparison
  | .eq => .Eq
  | .ne => .Ne
  | .lt => .Lt
  | .le => .Le
  | .gt => .Gt
  | .ge => .Ge

def toImportFix : ImportFix → lint.ImportFix
  | .keep => .Keep
  | .remove => .Remove
  | .byName => .ByName

def toLintLevel : LintLevel → lint.Level
  | .allow => .Allow
  | .expect => .Expect
  | .warn => .Warn
  | .deny => .Deny
  | .forbid => .Forbid

def toCase : Case → lint.Case
  | .snake => .Snake
  | .camel => .Camel
  | .upper => .Upper

def toNamed : Named → lint.Named
  | .module => .Module
  | .component => .Component
  | .variable => .Variable
  | .field => .Field
  | .binder => .Binder
  | .function => .Function
  | .instance => .Instance
  | .constraint => .Constraint
  | .global => .Global
  | .enumeration => .Enumeration
  | .variant => .Variant
  | .record => .Record
  | .abstractType => .AbstractType
  | .constant => .Constant

impl lint_severity: lint::severity for (l : LintLevel) {
  level := toLintLevel l,
  result := toLevel l.severity?,
}

impl lint_setting: lint::setting for (c r : LintLevel) {
  current := toLintLevel c,
  requested := toLintLevel r,
  accepted? := (setLevel c r).1,
  level := toLintLevel (setLevel c r).2,
}

impl lint_effective: lint::effective for (d : LintLevel) (cs : Bool) (c : LintLevel) (ss : Bool) (s : LintLevel) {
  default_level := toLintLevel d,
  cli_set? := cs,
  cli := toLintLevel c,
  src_set? := ss,
  src := toLintLevel s,
  after_cli := toLintLevel (effectiveLevel d (if cs then some c else none) none).1,
  level := toLintLevel (effectiveLevel d (if cs then some c else none) (if ss then some s else none)).1,
  error? := (effectiveLevel d (if cs then some c else none) (if ss then some s else none)).2,
}

-- Over `Nat`, so `decide` does not apply: a proof by cases.
impl lint_unused_import: lint::unused_import for (g : Bool) (n : Nat) (f : Bool) {
  glob? := g,
  n_paths := n,
  first? := f,
  unused? := unusedImport g n f,
} by
  intro g n f _
  cases g <;> cases f <;> rcases n with _ | n <;> simp [fren_spec, unusedImport] <;> omega

impl lint_naming_case: lint::naming_case for (w : Named) {
  what := toNamed w,
  case := toCase w.case,
}

namespace Patterns
open Fren.Core

theorem upper_not_lower (c : Char) (h : isUpperAscii c = true) : isLowerAscii c = false := by
  simp [isUpperAscii, isLowerAscii] at *
  intro h1
  have := Char.le_trans h.2 (show 'Z' ≤ 'a' by decide)
  exact absurd (Char.le_antisymm this h1) (by intro e; subst e; simp at h)

/-- `.*[A-Z].*`: some character is an uppercase letter. -/
theorem snake_pattern (cs : List Char) :
    (Re.cat (.star .any) (.cat (.cls false [('A', 'Z')]) (.star .any))).mat cs = cs.any isUpperAscii := by
  rw [Re.mat_cat_star_any]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, Re.mat_cat_cls, Re.mat_star_any]
  constructor
  · rintro ⟨i, _, h⟩
    cases hd : cs.drop i with
    | nil => simp [hd] at h
    | cons c t =>
      simp [hd, inRanges] at h
      exact ⟨c, List.mem_of_mem_drop (i := i) (by rw [hd]; simp), by simpa [isUpperAscii] using h⟩
  · rintro ⟨c, hc, hu⟩
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hc
    refine ⟨l1.length, by simp; omega, ?_⟩
    simp [List.drop_left', inRanges]
    simpa [isUpperAscii] using hu

theorem char_eq_of_le (c d : Char) : (d ≤ c ∧ c ≤ d) ↔ c = d :=
  ⟨fun ⟨h1, h2⟩ => Char.le_antisymm h2 h1, fun h => h ▸ ⟨Char.le_refl _, Char.le_refl _⟩⟩

theorem upper_ne_underscore (c : Char) (h : isUpperAscii c = true) : c ≠ '_' := by
  intro e; subst e; simp [isUpperAscii] at h

/-- `[A-Z][^_]*`: it starts with an uppercase letter, and has no `_`. -/
theorem camel_pattern (cs : List Char) :
    (Re.cat (.cls false [('A', 'Z')]) (.star (.cls true [('_', '_')]))).mat cs =
      (cs.head?.any isUpperAscii && !cs.contains '_') := by
  rw [Re.mat_cat_cls]
  cases cs with
  | nil => simp
  | cons c t =>
    dsimp only
    rw [Re.mat_star_cls]
    apply Bool.eq_iff_iff.mpr
    simp only [inRanges, List.any_cons, List.any_nil, Bool.or_false, bne_iff_ne, ne_eq, Bool.and_eq_true,
      List.all_eq_true, List.head?_cons, Option.any_some, Bool.not_eq_true', List.contains_cons]
    constructor
    · rintro ⟨h1, h2⟩
      have hu : isUpperAscii c = true := by simpa [isUpperAscii] using h1
      have hn : '_' ∉ t := fun hm => by have := h2 '_' hm; simp at this
      have hc : c ≠ '_' := upper_ne_underscore c hu
      simp [hu, hn, Ne.symm hc]
    · rintro ⟨hu, h2⟩
      have hn : '_' ∉ t := by intro hm; simp [hm] at h2
      refine ⟨by simpa [isUpperAscii] using hu, fun d hd h => ?_⟩
      have : d = '_' := (char_eq_of_le d '_').mp (by simpa using h)
      exact hn (this ▸ hd)

/-- `[A-Z][^a-z]*`: it starts with an uppercase letter, and has no lowercase
letter. -/
theorem upper_pattern (cs : List Char) :
    (Re.cat (.cls false [('A', 'Z')]) (.star (.cls true [('a', 'z')]))).mat cs =
      (cs.head?.any isUpperAscii && !cs.any isLowerAscii) := by
  rw [Re.mat_cat_cls]
  cases cs with
  | nil => simp
  | cons c t =>
    dsimp only
    rw [Re.mat_star_cls]
    apply Bool.eq_iff_iff.mpr
    simp only [inRanges, List.any_cons, List.any_nil, Bool.or_false, bne_iff_ne, ne_eq, Bool.and_eq_true,
      List.all_eq_true, List.head?_cons, Option.any_some, Bool.not_eq_true']
    constructor
    · rintro ⟨h1, h2⟩
      have hu : isUpperAscii c = true := by simpa [isUpperAscii] using h1
      refine ⟨hu, ?_⟩
      simp only [Bool.or_eq_false_iff, List.any_eq_false]
      refine ⟨upper_not_lower c hu, fun d hd hl => ?_⟩
      exact h2 d hd (by simpa [isLowerAscii] using hl)
    · rintro ⟨hu, h2⟩
      simp only [Bool.or_eq_false_iff, List.any_eq_false] at h2
      refine ⟨by simpa [isUpperAscii] using hu, fun d hd h => ?_⟩
      exact h2.2 d hd (by simpa [isLowerAscii] using h)

end Patterns

-- For every name, with `nameInCase`, which the naming lints use, against
-- what the spec's patterns mean.
impl lint_in_case: lint::in_case for (c : Case) (s : String) {
  case := toCase c,
  name := s,
  conventional? := Fren.Core.nameInCase s c,
} by
  intro c s _
  cases c <;> simp [fren_spec, Fren.Core.nameInCase, Fren.Core.inCase, toCase, Fren.Core.Re.matches,
    Patterns.snake_pattern, Patterns.camel_pattern, Patterns.upper_pattern]

impl lint_expectation: lint::expectation for (n : Nat) (l : LintLevel) {
  n_fired := n,
  level := toLintLevel l,
  fulfilled? := expectationFulfilled n,
  reported? := expectationReported n l,
} by
  intro n l _
  cases l <;> rcases n with _ | n <;> simp [fren_spec, expectationFulfilled, expectationReported, toLintLevel]
    <;> first | decide | omega

-- Over `Nat`, so `decide` does not apply: a proof by cases.
impl lint_import_fix: lint::import_fix for (u g fu fg : Bool) (n : Nat) {
  unused? := u,
  glob? := g,
  fix_unused? := fu,
  fix_glob? := fg,
  n_used := n,
  fix := toImportFix (importFix u g fu fg n),
} by
  intro u g fu fg n _
  cases u <;> cases g <;> cases fu <;> cases fg <;> rcases n with _ | n <;> simp [fren_spec, importFix, toImportFix]

impl lint_fix_exit: lint::fix_exit for (c l f : Bool) {
  check? := c,
  loaded? := l,
  unchanged? := f,
  code := (fixExit c l f).toNat,
}

-- A list of lints is the lints given, in order, with repeats.
interp lint::Lint := Fren.Core.Lint

instance : LawfulBEq Fren.Core.Lint where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

-- For every lint and lists given, with `fixSelected`, which `fren fix` uses:
-- the spec sees each list's set of lints, so a repeated lint is harmless.
impl lint_fix_selected: lint::fix_selected for (l : Fren.Core.Lint) (only skip : Array Fren.Core.Lint) {
  lint := l,
  only := Fren.FinSet.ofArray only,
  skip := Fren.FinSet.ofArray skip,
  fixed? := fixSelected only skip l,
} by
  intro l only skip _
  simp [fren_spec, fixSelected]

-- Over `Nat`, so `decide` does not apply: a proof by cases.
impl lint_dead_item: lint::dead_item for (w : Named) (p : Bool) (n : Nat) {
  what := toNamed w,
  pub? := p,
  n_uses := n,
  dead? := deadItem w p n,
} by
  intro w p n _
  cases w <;> cases p <;> rcases n with _ | n <;> simp [fren_spec, deadItem, toNamed] <;> omega

impl lint_literal_comparison: lint::literal_comparison for (e l : Bool) {
  equal? := e,
  literal? := l,
  negated? := literalNegated e l,
}

impl lint_complement: lint::complement for (c : Comparison) {
  op := toComparison c,
  result := toComparison c.complement,
}

-- Both front ends report `undecidable` exactly when `inCore` is false.
impl lint_undecidable_fires: lint::undecidable_fires for (c : Fren.Core.Construct) (a m i g f r l : Bool) {
  construct := toConstruct c,
  constant_args? := a,
  comparable? := m,
  infinite_output? := i,
  ground? := g,
  infinite_elems? := f,
  finite_range? := r,
  literal_operand? := l,
  fires? := !Fren.Core.inCore c a m i g f r l,
} by
  intro c a m i g f r l _
  simp only [fren_spec]
  -- The instance's `decidable?` is `inCore`'s, by `in_core`'s rule.
  refine ⟨_, a, m, i, g, f, r, l, Fren.Core.inCore c a m i g f r l, by simp, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, trivial, ?_⟩
  cases c <;> simp [toConstruct, Fren.Core.inCore]

/-! ## Collections, outputs and indexes -/

-- Both front ends decide `length_zero` and `card_zero` with `lengthZero`.
impl length_zero: lint::length_zero for (c : Comparison) (b : Int) {
  op := toComparison c,
  bound := b,
  fires? := (Fren.Core.lengthZero c b).1,
  empty? := (Fren.Core.lengthZero c b).2,
} by
  intro c b _
  cases c <;> simp [fren_spec, toComparison, Fren.Core.lengthZero]

impl membership_chain: lint::membership_chain for (n : Nat) (same : Bool) {
  n := n,
  same_left? := same,
  fires? := Fren.Core.membershipChainFires n same,
} by
  intro n same _
  cases same <;> simp [fren_spec, Fren.Core.membershipChainFires] <;> omega

impl output_lints: lint::output_lints for (d v : Bool) (r : Nat) (eq : Bool) {
  defined? := d,
  mentions? := v,
  n_reqs := r,
  equation? := eq,
  constant? := (Fren.Core.outputLints d v r eq).1,
  definable? := (Fren.Core.outputLints d v r eq).2,
} by
  intro d v r eq _
  cases d <;> cases v <;> cases eq <;> simp [fren_spec, Fren.Core.outputLints] <;> omega

impl index_after_use: lint::index_after_use for (l r : Bool) {
  indexes_left? := l,
  bounds_right? := r,
  fires? := Fren.Core.indexAfterUse l r,
}

end Fren.Impls
