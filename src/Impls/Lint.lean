-- keep-sorted start
import Impls.Lang
import Impls.View
import Reqs.Lint
-- keep-sorted end
open Fren.Lang

/-! # Lints (`Reqs/Lint`) -/

namespace Fren.Impls

open Fren.Core (LintLevel Group Case Named ImportFix setLevel effectiveLevel groupAccepted outsideLevel unusedImport
  inCase expectationFulfilled expectationReported importFix fixExit fixSelected Comparison deadItem literalNegated Head)

instance : Fren.Finite LintLevel :=
  ⟨[.allow, .expect, .warn, .deny, .forbid], by intro x; cases x <;> simp⟩

instance : Fren.Finite Case := ⟨[.snake, .camel, .upper], by intro x; cases x <;> simp⟩

instance : Fren.Finite Group := ⟨Group.all.toList, by intro x; cases x <;> simp [Group.all]⟩

instance : Fren.Finite Named :=
  ⟨[.module, .component, .variable, .field, .binder, .function, .instance, .constraint, .global, .enumeration,
    .variant, .record, .abstractType, .typeAlias, .constant],
    by intro x; cases x <;> simp⟩

instance : Fren.Finite Comparison := ⟨Comparison.all.toList, by intro x; cases x <;> simp [Comparison.all]⟩

instance : Fren.Finite Head := ⟨[.not, .unequal, .ite, .when, .unless, .other], by intro x; cases x <;> simp⟩

instance : Fren.Finite Fren.Core.MemberKind :=
  ⟨[.use, .input, .output, .assumption, .inst, .guarantee, .expectation, .cover], by intro x; cases x <;> simp⟩

def toComparison : Comparison → lint.Comparison
  | .eq => .Eq
  | .ne => .Ne
  | .lt => .Lt
  | .le => .Le
  | .gt => .Gt
  | .ge => .Ge

def toHead : Head → lint.Head
  | .not => .Not
  | .unequal => .Unequal
  | .ite => .If
  | .when => .When
  | .unless => .Unless
  | .other => .Other

def toOffset : Fren.Core.Offset → lint.Offset
  | .zero => .Zero
  | .plusOne => .PlusOne
  | .minusOne => .MinusOne

def toImportFix : ImportFix → lint.ImportFix
  | .keep => .Keep
  | .remove => .Remove
  | .byName => .ByName

def toArmsFix : Fren.Core.ArmsFix → lint.ArmsFix
  | .merge => .Merge
  | .remove => .Remove
  | .replace => .Replace

def toLintLevel : LintLevel → lint.Level
  | .allow => .Allow
  | .expect => .Expect
  | .warn => .Warn
  | .deny => .Deny
  | .forbid => .Forbid

def toGroup : Group → lint.Group
  | .unused => .Unused
  | .nonstandardStyle => .NonstandardStyle
  | .style => .Style
  | .complexity => .Complexity
  | .suspicious => .Suspicious
  | .pedantic => .Pedantic
  | .restriction => .Restriction
  | .decidability => .Decidability

def toMemberKind : Fren.Core.MemberKind → lint.MemberKind
  | .use => .Use
  | .input => .Input
  | .output => .Output
  | .assumption => .Assumption
  | .inst => .Instance
  | .guarantee => .Guarantee
  | .expectation => .Expectation
  | .cover => .Cover

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
  | .typeAlias => .TypeAlias
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

impl lint_group_default: lint::group_default for (g : Group) {
  group := toGroup g,
  level := toLintLevel g.default,
}

-- Over `Nat`, so `decide` does not apply: a proof by cases. Both front ends
-- decide a group's setting with `groupAccepted`, in `LintTarget.rejectedBy?`.
impl lint_group_setting: lint::group_setting for (c : LintLevel) (n : Nat) (r : LintLevel) {
  current := toLintLevel c,
  n_forbidden := n,
  requested := toLintLevel r,
  accepted? := groupAccepted n r,
  level := toLintLevel (if groupAccepted n r then r else c),
} by
  intro c n r _
  cases c <;> cases r <;> rcases n with _ | n <;> simp +decide [fren_spec, groupAccepted, toLintLevel] <;> omega

impl lint_outside_options: lint::outside_options for (d : LintLevel) (os : Bool) (o : LintLevel) (gs : Bool) (g : LintLevel) {
  default_level := toLintLevel d,
  own_set? := os,
  own := toLintLevel o,
  group_set? := gs,
  group := toLintLevel g,
  level := toLintLevel (outsideLevel d (if os then some o else none) (if gs then some g else none)),
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
impl length_zero: lint::length_zero for (c : Comparison) (b : Int) (l : Bool) {
  op := toComparison c,
  bound := b,
  left? := l,
  fires? := (Fren.Core.lengthZero c b l).1,
  empty? := (Fren.Core.lengthZero c b l).2,
} by
  intro c b l _
  cases c <;> cases l <;> simp [fren_spec, toComparison, Fren.Core.lengthZero, Fren.Core.Comparison.mirror]

-- Both front ends decide `absurd_extreme_comparisons` with `absurdComparison`.
impl absurd_extreme_comparisons: lint::absurd_extreme_comparisons for (c : Comparison) (b : Int) (l : Bool) {
  op := toComparison c,
  bound := b,
  left? := l,
  fires? := (Fren.Core.absurdComparison c b l).1,
  value? := (Fren.Core.absurdComparison c b l).2,
} by
  intro c b l _
  cases c <;> cases l <;> simp [fren_spec, toComparison, Fren.Core.absurdComparison, Fren.Core.Comparison.mirror] <;> omega

impl membership_chain: lint::membership_chain for (n : Nat) (same later : Bool) {
  n := n,
  same_left? := same,
  later_indexes? := later,
  fires? := Fren.Core.membershipChainFires n same later,
} by
  intro n same later _
  cases same <;> cases later <;> simp [fren_spec, Fren.Core.membershipChainFires] <;> omega

impl output_lints: lint::output_lints for (d v : Bool) (r : Nat) (eq : Bool) {
  defined? := d,
  mentions? := v,
  n_guarantees := r,
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

/-! ## Conditionals -/

-- Both front ends decide with `Ex.simplerForm`, whose rules for these lints
-- fire when these functions say, given `negatedCond_isSome`.
impl unless_not: lint::unless_not for (n : Bool) (c : Head) {
  unless? := n,
  condition := toHead c,
  fires? := Fren.Core.unlessNot n c,
} by
  intro n c _
  cases n <;> cases c <;> simp [fren_spec, toHead, Fren.Core.unlessNot, Fren.Core.Head.negation]

impl collapsible_when: lint::collapsible_when for (n : Bool) (d : Head) {
  unless? := n,
  body := toHead d,
  fires? := Fren.Core.collapsibleWhen n d,
} by
  intro n d _
  cases n <;> cases d <;> simp [fren_spec, toHead, Fren.Core.collapsibleWhen]

impl if_not_else: lint::if_not_else for (c b : Head) {
  condition := toHead c,
  else_branch := toHead b,
  fires? := Fren.Core.ifNotElse c b,
} by
  intro c b _
  cases c <;> cases b <;> simp [fren_spec, toHead, Fren.Core.ifNotElse, Fren.Core.Head.negation]

/-! ## Matches -/

-- Both front ends group the arms with `sameArmGroups`, which joins two
-- arms by `sameArmsFires`, and fix a group by `sameArmsFix`.
impl match_same_arms: lint::match_same_arms for (s b w a : Bool) {
  same_body? := s,
  binds? := b,
  wildcard? := w,
  all? := a,
  fires? := Fren.Core.sameArmsFires s b,
  fix := toArmsFix (Fren.Core.sameArmsFix a w),
} by
  intro s b w a _
  cases s <;> cases b <;> cases w <;> cases a <;> simp [fren_spec, Fren.Core.sameArmsFires, Fren.Core.sameArmsFix, toArmsFix]

impl match_like_membership: lint::match_like_membership
    for (bb bs d tf ff et ef w wt : Bool) (t f : Nat) {
  bool_bodies? := bb,
  binds? := bs,
  disjoint? := d,
  true_first? := tf,
  false_first? := ff,
  equatable_true? := et,
  equatable_false? := ef,
  wildcard? := w,
  wildcard_true? := wt,
  n_true := t,
  n_false := f,
  fires? := (Fren.Core.matchMembership bb bs d tf ff et ef w wt t f).1,
  negated? := (Fren.Core.matchMembership bb bs d tf ff et ef w wt t f).2.1,
  pattern_test? := (Fren.Core.matchMembership bb bs d tf ff et ef w wt t f).2.2,
} by
  intro bb bs d tf ff et ef w wt t f _
  simp [fren_spec, Fren.Core.matchMembership]

impl wildcard_single_variant: lint::wildcard_single_variant for (n : Nat) {
  n_matched := n,
  fires? := Fren.Core.wildcardSingle n,
} by
  intro n _
  simp [fren_spec, Fren.Core.wildcardSingle]
  omega

-- Both front ends decide `is_equality` and `irrefutable_is` with
-- `isEquality` and `irrefutableIs`, where they elaborate the test.
impl is_equality: lint::is_equality for (e i : Bool) {
  equatable? := e,
  irrefutable? := i,
  fires? := Fren.Core.isEquality e i,
} by
  intro e i _
  cases e <;> cases i <;> simp [fren_spec, Fren.Core.isEquality]

impl irrefutable_is: lint::irrefutable_is for (m : Bool) {
  matches_every? := m,
  fires? := Fren.Core.irrefutableIs m,
} by
  intro m _
  cases m <;> simp [fren_spec, Fren.Core.irrefutableIs]

-- Both front ends decide `chainable_comparison` with `chainableAt`, which
-- reads each pair of conjuncts with `chainableComparison`.
impl chainable_comparison: lint::chainable_comparison for (la ra ls rs lf fl ff ll : Bool) {
  left_ascending? := la,
  right_ascending? := ra,
  left_single? := ls,
  right_single? := rs,
  last_first? := lf,
  first_last? := fl,
  first_first? := ff,
  last_last? := ll,
  fires? := (Fren.Core.chainableComparison la ra ls rs lf fl ff ll).1,
  flip_left? := (Fren.Core.chainableComparison la ra ls rs lf fl ff ll).2.1,
  flip_right? := (Fren.Core.chainableComparison la ra ls rs lf fl ff ll).2.2,
} by
  intro la ra ls rs lf fl ff ll _
  simp [fren_spec, Fren.Core.chainableComparison]

/-! ## Matches and bindings -/

-- Both front ends decide `if_chain_match` with `ifChainMatch`, from the
-- chain's tests read by `sameScrutinee`, `repeatedVariants` and
-- `untestedVariants`.
impl if_chain_match: lint::if_chain_match for (n : Nat) (v : Bool) (r u : Nat) {
  n_tests := n,
  variant_tests? := v,
  n_repeated := r,
  n_untested := u,
  fires? := (Fren.Core.ifChainMatch n v r u).1,
  wildcard? := (Fren.Core.ifChainMatch n v r u).2,
} by
  intro n v r u _
  cases v <;> simp [fren_spec, Fren.Core.ifChainMatch] <;> omega

impl case_split_guarantees: lint::case_split_guarantees for (n r : Nat) {
  n_cases := n,
  n_repeated := r,
  fires? := Fren.Core.caseSplitGuarantees n r,
} by
  intro n r _
  simp [fren_spec, Fren.Core.caseSplitGuarantees] <;> omega

impl redundant_bindings: lint::redundant_bindings for (n v : String) {
  name := n,
  value := v,
  fires? := Fren.Core.redundantBinding n v,
} by
  intro n v _
  simpa [fren_spec, Fren.Core.redundantBinding] using eq_comm

/-! ## Suspicious expressions -/

instance : Fren.Finite Fren.Core.InfixOp :=
  ⟨Fren.Core.InfixOp.all.toList, by intro x; cases x <;> simp [Fren.Core.InfixOp.all]⟩

def toInfixOp : Fren.Core.InfixOp → lint.InfixOp
  | .iff => .Iff
  | .or => .Or
  | .and => .And
  | .eq => .Eq
  | .ne => .Ne
  | .lt => .Lt
  | .le => .Le
  | .gt => .Gt
  | .ge => .Ge
  | .in => .In
  | .subset => .Subset
  | .add => .Add
  | .sub => .Sub
  | .concat => .Concat
  | .union => .Union
  | .minus => .Minus
  | .mul => .Mul
  | .inter => .Inter
  | .join => .Join

def toEqOpValue : Fren.Core.EqOpValue → lint.EqOpValue
  | .alwaysTrue => .AlwaysTrue
  | .alwaysFalse => .AlwaysFalse
  | .zero => .Zero
  | .empty => .Empty
  | .operand => .Operand

-- Both front ends decide `eq_op`, and the value its message gives, with `eqOp`.
impl eq_op: lint::eq_op for (op : Fren.Core.InfixOp) (same : Bool) {
  op := toInfixOp op,
  same? := same,
  fires? := (Fren.Core.eqOp op same).isSome,
  value := toEqOpValue ((Fren.Core.eqOp op same).getD .operand),
} by
  intro op same _
  cases op <;> cases same <;> simp [fren_spec, toInfixOp, toEqOpValue, Fren.Core.eqOp]

-- Both front ends decide `eq_op` on `when` and `unless` with
-- `eqOpConditional`.
impl eq_op_conditional: lint::eq_op_conditional for (n same : Bool) {
  unless? := n,
  same? := same,
  fires? := (Fren.Core.eqOpConditional n same).isSome,
  value := toEqOpValue ((Fren.Core.eqOpConditional n same).getD .operand),
} by
  intro n same _
  cases n <;> cases same <;> simp [fren_spec, toEqOpValue, Fren.Core.eqOpConditional]

impl ifs_same_cond: lint::ifs_same_cond for (earlier : Bool) {
  earlier? := earlier,
  fires? := Fren.Core.ifsSameCond earlier,
}

impl same_branches: lint::same_branches for (same : Bool) {
  same? := same,
  fires? := Fren.Core.sameBranches same,
}

impl duplicate_elements: lint::duplicate_elements for (n : Nat) {
  n_repeats := n,
  fires? := Fren.Core.duplicateElements n,
} by
  intro n _
  simp [fren_spec, Fren.Core.duplicateElements]

impl empty_argument: lint::empty_argument for (m : Fren.Core.Method) (i : Nat) (e : Bool) {
  method := toMethod m,
  index := i,
  empty? := e,
  fires? := Fren.Core.emptyArgument m i e,
} by
  intro m i e _
  cases m <;> cases e <;> simp [fren_spec, toMethod, Fren.Core.emptyArgument] <;> omega

/-! ## Repeated constraints, invisible characters and negative positions -/

instance : Fren.Finite Fren.Core.ConstraintKind := ⟨[.assume, .ensure, .expect, .cover], by intro x; cases x <;> simp⟩

def toConstraintKind : Fren.Core.ConstraintKind → lint.ConstraintKind
  | .assume => .Assume
  | .ensure => .Ensure
  | .expect => .Expect
  | .cover => .Cover

-- Both front ends find the repeats with `repeatedConstraints`, and fix one
-- where `duplicateConstraint` says.
impl duplicate_constraint: lint::duplicate_constraint for (e l : Fren.Core.ConstraintKind) (same : Bool) {
  earlier := toConstraintKind e,
  later := toConstraintKind l,
  same? := same,
  fires? := (Fren.Core.duplicateConstraint e l same).1,
  fixed? := (Fren.Core.duplicateConstraint e l same).2,
} by
  intro e l same _
  cases e <;> cases l <;> cases same <;> simp [fren_spec, toConstraintKind, Fren.Core.duplicateConstraint] <;> decide

-- Both front ends find the characters with `invisibleFix?`, which reports
-- those that `invisibleCode` says.
impl invisible_character: lint::invisible_character for (n : Nat) (c : Bool) {
  code := n,
  comment? := c,
  fires? := Fren.Core.invisibleCode c n,
} by
  intro n c _
  cases c <;> simp [fren_spec, Fren.Core.invisibleCode] <;> omega

-- Both front ends decide an argument with `negativePosition`, and an index
-- with `negativeLiteral?` alone, as `negativePosition` does for an index.
impl negative_position: lint::negative_position for (x : Bool) (m : Fren.Core.Method) (i : Nat) (neg : Bool) {
  index? := x,
  method := toMethod m,
  arg := i,
  negative? := neg,
  fires? := Fren.Core.negativePosition x m i neg,
} by
  intro x m i neg _
  cases x <;> cases m <;> cases neg <;> simp [fren_spec, toMethod, Fren.Core.negativePosition] <;> omega

/-! ## Operators and methods -/

instance : Fren.Finite Ordering := ⟨[.lt, .eq, .gt], by intro x; cases x <;> simp⟩

instance : Fren.Finite Fren.Core.IdentityOperator :=
  ⟨[.add, .sub, .mul, .concat, .union, .minus], by intro x; cases x <;> simp⟩

instance : Fren.Finite Fren.Core.IdentityOperand := ⟨[.zero, .one, .empty, .negation, .other], by intro x; cases x <;> simp⟩

def toOrder : Ordering → lint.Order
  | .lt => .Below
  | .eq => .Same
  | .gt => .Above

def toIndexTest : Fren.Core.IndexTest → lint.IndexTest
  | .found => .Found
  | .absent => .Absent
  | .atStart => .AtStart
  | .other => .Other

def toAssoc : Fren.Core.Assoc → lang.Assoc
  | .left => .Left
  | .right => .Right
  | .nonAssoc => .NonAssoc

def toIdentityOperator : Fren.Core.IdentityOperator → lint.IdentityOperator
  | .add => .Add
  | .sub => .Sub
  | .mul => .Mul
  | .concat => .Concat
  | .union => .Union
  | .minus => .Minus

def toIdentityOperand : Fren.Core.IdentityOperand → lint.IdentityOperand
  | .zero => .Zero
  | .one => .One
  | .empty => .Empty
  | .negation => .Negation
  | .other => .Other

def toRewrite : Fren.Core.Rewrite → lint.Rewrite
  | .keepLeft => .KeepLeft
  | .keepRight => .KeepRight
  | .flip => .Flip
  | .unchanged => .Unchanged

impl comparison_holds: lint::comparison_holds for (c : Comparison) (o : Ordering) {
  op := toComparison c,
  order := toOrder o,
  holds? := c.holds o,
}

-- Both front ends decide `double_comparison` with `doubleComparison`.
impl double_comparison: lint::double_comparison for (conj : Bool) (l r : Comparison) {
  conjunction? := conj,
  first := toComparison l,
  second := toComparison r,
  fires? := (Fren.Core.doubleComparison conj l r).isSome,
  result := toComparison ((Fren.Core.doubleComparison conj l r).getD l),
}

-- Both front ends decide `contradictory_comparisons` with these, in
-- `opReports`.
impl contradictory_chain: lint::contradictory_chain for (c1 : Comparison) (a : Int) (c2 : Comparison) (b : Int) {
  first := toComparison c1,
  first_bound := a,
  second := toComparison c2,
  second_bound := b,
  fires? := Fren.Core.contradictoryChain c1 a c2 b,
} by
  intro c1 a c2 b _
  cases c1 <;> cases c2 <;>
    simp [fren_spec, toComparison, Fren.Core.contradictoryChain, Fren.Core.contradictoryComparisons,
      Fren.Core.disjointBounds, Fren.Core.Comparison.mirror, Fren.Core.Comparison.boundsBelow,
      Fren.Core.Comparison.boundsAbove, Fren.Core.Comparison.least, Fren.Core.Comparison.greatest] <;> omega

impl contradictory_comparisons: lint::contradictory_comparisons for (conj : Bool) (c1 : Comparison) (a : Int)
    (c2 : Comparison) (b : Int) {
  conjunction? := conj,
  first := toComparison c1,
  first_bound := a,
  second := toComparison c2,
  second_bound := b,
  fires? := Fren.Core.contradictoryComparisons conj c1 a c2 b,
} by
  intro conj c1 a c2 b _
  cases conj <;> cases c1 <;> cases c2 <;>
    simp [fren_spec, toComparison, Fren.Core.contradictoryComparisons, Fren.Core.disjointBounds,
      Fren.Core.Comparison.complement, Fren.Core.Comparison.boundsBelow, Fren.Core.Comparison.boundsAbove,
      Fren.Core.Comparison.least, Fren.Core.Comparison.greatest] <;> omega

impl contradictory_equalities: lint::contradictory_equalities for (conj : Bool) (c1 c2 : Comparison) (d : Bool) {
  conjunction? := conj,
  first := toComparison c1,
  second := toComparison c2,
  distinct? := d,
  fires? := Fren.Core.contradictoryEqualities conj c1 c2 d,
}

-- Both front ends decide `redundant_comparisons` with `redundantComparisons`.
impl redundant_comparisons: lint::redundant_comparisons for (conj : Bool) (c1 : Comparison) (a : Int)
    (c2 : Comparison) (b : Int) {
  conjunction? := conj,
  first := toComparison c1,
  first_bound := a,
  second := toComparison c2,
  second_bound := b,
  fires? := (Fren.Core.redundantComparisons conj c1 a c2 b).1,
  keep_first? := (Fren.Core.redundantComparisons conj c1 a c2 b).2,
} by
  intro conj c1 a c2 b _
  cases c1 <;> cases c2 <;>
    simp [fren_spec, toComparison, Fren.Core.redundantComparisons, Fren.Core.disjointBounds,
      Fren.Core.Comparison.complement, Fren.Core.Comparison.boundsBelow, Fren.Core.Comparison.boundsAbove,
      Fren.Core.Comparison.least, Fren.Core.Comparison.greatest] <;> omega

impl bool_equality: lint::bool_equality for (c : Comparison) (b l : Bool) {
  op := toComparison c,
  bools? := b,
  literal? := l,
  fires? := Fren.Core.boolEquality c b l,
}

impl index_test: lint::index_test for (c : Comparison) (b p : Int) {
  op := toComparison c,
  bound := b,
  position := p,
  test := toIndexTest (Fren.Core.indexTest c b),
} by
  intro c b p _
  cases c <;> by_cases h0 : b = 0 <;> by_cases h1 : b = -1 <;> simp_all [fren_spec, toComparison, Fren.Core.indexTest, toIndexTest]

-- The instance's `bare?` is `bareOperand`, which meets `operand`'s rules.
impl else_extends: lint::else_extends for (o i : Nat) (a : Fren.Core.Assoc) (r : Bool) {
  outer := o,
  inner := i,
  assoc := toAssoc a,
  right? := r,
  fires? := Fren.Core.elseExtends o i a r,
} by
  intro o i a r _
  simp only [fren_spec]
  refine ⟨_, _, _, _, Fren.Core.bareOperand o i a r, by simp [Fren.Core.elseExtends], ⟨rfl, rfl, rfl, rfl⟩, trivial, ?_⟩
  simp only [Fren.Core.bareOperand]
  cases a <;> cases r <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [toAssoc] <;> omega

impl identity_op: lint::identity_op for (o : Fren.Core.IdentityOperator) (l r : Fren.Core.IdentityOperand) {
  op := toIdentityOperator o,
  left := toIdentityOperand l,
  right := toIdentityOperand r,
  rewrite := toRewrite (Fren.Core.identityRewrite o l r),
}

-- Both front ends decide `erasing_op` with `erasingOp`, in `opReports`.
impl erasing_op: lint::erasing_op for (op : Fren.Core.InfixOp) (l r : Fren.Core.IdentityOperand) (same : Bool) {
  op := toInfixOp op,
  left := toIdentityOperand l,
  right := toIdentityOperand r,
  same? := same,
  fires? := Fren.Core.erasingOp op l r same,
}

/-! ## Arithmetic and parentheses -/

-- Both front ends decide these with `arithReports`, which asks the pure
-- functions below.
impl double_neg: lint::double_neg for (n : Bool) {
  negated_operand? := n,
  fires? := Fren.Core.doubleNeg n,
}

impl neg_multiply: lint::neg_multiply for (a b : Bool) {
  left_minus_one? := a,
  right_minus_one? := b,
  fires? := (Fren.Core.negMultiply a b).1,
  negate_left? := (Fren.Core.negMultiply a b).2,
} by
  intro a b _
  cases a <;> cases b <;> simp [fren_spec, Fren.Core.negMultiply]

impl int_plus_one: lint::int_plus_one for (c : Comparison) (l r : Fren.Core.Offset) {
  op := toComparison c,
  left := toOffset l,
  right := toOffset r,
  fires? := (Fren.Core.intPlusOne c l r).1,
  result := toComparison (Fren.Core.intPlusOne c l r).2.1,
  drop_left? := (Fren.Core.intPlusOne c l r).2.2,
} by
  intro c l r _
  cases c <;> cases l <;> cases r <;> simp [fren_spec, toComparison, toOffset, Fren.Core.intPlusOne]

impl int_plus_one_in_chain: lint::int_plus_one_in_chain for (d : Bool) (i n : Nat) {
  comparison := i,
  n_comparisons := n,
  drop_left? := d,
  fires? := Fren.Core.intPlusOneInChain d i n,
} by
  intro d i n _
  cases d <;> simp [fren_spec, Fren.Core.intPlusOneInChain] <;> omega

impl double_parens: lint::double_parens for (d : Nat) {
  depth := d,
  fires? := Fren.Core.doubleParens d,
} by
  intro d _
  simp [fren_spec, Fren.Core.doubleParens]
  omega

-- Both front ends decide these with `opReports`, which asks the pure
-- functions below.
impl needless_bool_assign: lint::needless_bool_assign for (e t : Bool) {
  else_negates? := e,
  then_negates? := t,
  fires? := (Fren.Core.needlessBoolAssign e t).1,
  unequal? := (Fren.Core.needlessBoolAssign e t).2,
} by
  intro e t _
  cases e <;> cases t <;> simp [fren_spec, Fren.Core.needlessBoolAssign]

impl suspicious_unary_op_formatting: lint::suspicious_unary_op_formatting for (p a s : Bool) {
  punctuator? := p,
  adjacent? := a,
  spaced? := s,
  fires? := Fren.Core.suspiciousUnaryOp p a s,
}

/-! ## Methods, patterns, types and matches -/

def toChainFix : Fren.Core.ChainFix → lint.ChainFix
  | .keep => .Keep
  | .receiver => .Receiver
  | .single _ => .Single

-- Both front ends shorten a chain with `shortestChain`, which rewrites the
-- pairs that `methodChain` does.
impl method_chain: lint::method_chain for (i o : Fren.Core.Method) {
  inner := toMethod i,
  outer := toMethod o,
  fix := toChainFix (Fren.Core.methodChain i o),
  single := match Fren.Core.methodChain i o with
    | .single m => toMethod m
    | _ => toMethod o,
}

-- For every name, as `checkVarName` reads its suffix.
impl redundant_bool_type: lint::redundant_bool_type for (s : String) (a : lang.Annot) {
  name := s,
  annot := a,
  fires? := Fren.Core.redundantBoolType (.mkSimple s) (isBool? a),
} by
  intro s a _
  have hs : Fren.Core.nameText (.mkSimple s) = s := rfl
  cases h : Fren.Str.endsWith s "?" <;> cases a <;> simp [fren_spec, Fren.Core.redundantBoolType, isBool?, hs, h]

impl trivial_match: lint::trivial_match for (n : Nat) (b : Bool) {
  n_arms := n,
  binds? := b,
  fires? := Fren.Core.trivialMatch n b,
} by
  intro n b _
  cases b <;> simp [fren_spec, Fren.Core.trivialMatch] <;> omega

impl zero_sized_map_values: lint::zero_sized_map_values for (e : Bool) (n : Nat) (p : Bool) {
  enum? := e,
  n_variants := n,
  payload? := p,
  fires? := Fren.Core.zeroSizedMapValues e n p,
} by
  intro e n p _
  cases e <;> cases p <;> simp [fren_spec, Fren.Core.zeroSizedMapValues] <;> omega

impl many_single_char_names: lint::many_single_char_names for (n : Nat) {
  n := n,
  fires? := Fren.Core.manySingleCharNames n,
} by
  intro n _
  simp [fren_spec, Fren.Core.manySingleCharNames] <;> omega

-- `namesSimilar` reads the names' characters into these.
impl similar_names: lint::similar_names for (a b : Nat) (o d w l : Bool) {
  len_a := a,
  len_b := b,
  one_edit? := o,
  digits? := d,
  word? := w,
  allowed? := l,
  fires? := Fren.Core.similarNames a b o d w l,
} by
  intro a b o d w l _
  cases o <;> cases d <;> cases w <;> cases l <;> simp [fren_spec, Fren.Core.similarNames] <;> omega

-- `codeLines` counts the lines.
impl too_many_lines: lint::too_many_lines for (n : Nat) {
  n_lines := n,
  fires? := Fren.Core.tooManyLines n,
} by
  intro n _
  simp [fren_spec, Fren.Core.tooManyLines] <;> omega

-- Both front ends decide with `needlessMatch`, from what `givesBack` says
-- of each arm.
impl needless_match: lint::needless_match for (g w s t : Bool) {
  given_back? := g,
  wildcard? := w,
  scrutinee_back? := s,
  trivial? := t,
  fires? := Fren.Core.needlessMatch g w s t,
} by
  intro g w s t _
  cases g <;> cases w <;> cases s <;> cases t <;> simp [fren_spec, Fren.Core.needlessMatch]

-- Both front ends decide what it mentions with `mentionsAny`, as for
-- `constant_output`.
impl assertions_on_constants: lint::assertions_on_constants for (m : Bool) {
  mentions? := m,
  fires? := Fren.Core.assertionOnConstant m,
} by
  intro m _
  cases m <;> simp [fren_spec, Fren.Core.assertionOnConstant]

-- `trivialPattern?` reads the pattern's characters; the spec states the
-- same with a pattern, which the tests check against it.
tested lint::trivial_pattern: "test/ui/lints/methods.fren", "test/cli/lints/style/f0744_trivial_pattern.fren"

impl module_inception: lint::module_inception for (n p : String) {
  name := n,
  parent := p,
  fires? := Fren.Core.moduleInception n p,
} by
  intro n p _
  simp [fren_spec, Fren.Core.moduleInception]

impl enum_variant_names: lint::enum_variant_names for (n : Nat) (f l : Bool) {
  n_variants := n,
  shared_first? := f,
  shared_last? := l,
  fires? := Fren.Core.enumVariantNames n f l,
} by
  intro n f l _
  cases f <;> cases l <;> simp [fren_spec, Fren.Core.enumVariantNames] <;> omega

impl variant_has_enum_name: lint::variant_has_enum_name for (n e : Nat) (c : Bool) {
  n_words := n,
  n_enum_words := e,
  contains? := c,
  fires? := Fren.Core.variantHasEnumName n e c,
} by
  intro n e c _
  cases c <;> simp [fren_spec, Fren.Core.variantHasEnumName] <;> omega

-- Over strings, as for `trivial_pattern`: the patterns of the rules against
-- `upperCaseAcronyms`, `justUnderscoresAndDigits` and `disallowedName`.
tested lint::upper_case_acronyms: "test/ui/lints/names.fren", "test/cli/lints/style/f0750_upper_case_acronyms.fren"
tested lint::just_underscores_and_digits: "test/ui/lints/names.fren",
  "test/cli/lints/style/f0751_just_underscores_and_digits.fren"
tested lint::disallowed_names: "test/ui/lints/names.fren", "test/cli/lints/style/f0752_disallowed_names.fren"

/-! ## Strings, sequences and patterns -/

/-! The meaning of the methods, from `Fren.Str`, at the values that the
lints of strings rewrite. -/

namespace Str
open Fren.Str

theorem one_char (t : String) (h : t.length = 1) : ∃ c, t.toList = [c] := by
  rw [← String.length_toList] at h
  exact List.length_eq_one_iff.mp h

theorem at_zero (s t : String) (h : len t = 1) : Fren.Str.at s 0 = t ↔ startsWith s t = true := by
  rw [Fren.Str.startsWith_iff]
  obtain ⟨c, hc⟩ := one_char t (by simp [len] at h; omega)
  simp only [Fren.Str.at, slice, String.ext_iff, hc]
  rcases hs : s.toList with _ | ⟨d, rest⟩
  · simp [← String.length_toList, hs, eq_comm]
  · simp [← String.length_toList, hs, eq_comm]

theorem at_last (s t : String) (h : len t = 1) : Fren.Str.at s (len s - 1) = t ↔ endsWith s t = true := by
  rw [Fren.Str.endsWith_iff]
  obtain ⟨c, hc⟩ := one_char t (by simp [len] at h; omega)
  simp only [Fren.Str.at, slice, len, String.ext_iff, hc]
  rcases List.eq_nil_or_concat s.toList with hs | ⟨l, d, hs⟩
  · simp [← String.length_toList, hs, eq_comm]
  · simp [← String.length_toList, hs, eq_comm]
    rw [if_pos (by omega)]; simp

theorem slice_whole (s : String) : slice s 0 (len s) = s := by
  simp only [slice, len, String.ext_iff]
  rcases hs : s.toList with _ | ⟨d, rest⟩
  · simp [← String.length_toList, hs]
  · simp [← String.length_toList, hs]

theorem replaceAllAux_self (fuel : Nat) (cs a : List Char) : replaceAllAux fuel cs a a = cs := by
  induction fuel generalizing cs with
  | zero => simp [replaceAllAux]
  | succ fuel ih =>
    cases cs with
    | nil => simp [replaceAllAux]
    | cons c rest =>
      simp only [replaceAllAux]
      split
      · rename_i h
        rw [ih]
        obtain ⟨t, ht⟩ := List.isPrefixOf_iff_prefix.mp h
        rw [← ht]; simp
      · rw [ih]

theorem replaceAll_self (s a : String) : replaceAll s a a = s := by
  simp only [replaceAll]
  split
  · rfl
  · rw [replaceAllAux_self]; exact String.ofList_toList

theorem replace_self (s a : String) : replace s a a = s := by
  simp only [replace]
  split
  · rename_i h
    have : a = "" := by simpa using h
    subst this; simp
  · simp only [indexOf]
    split
    · split
      · rename_i k hk
        have hp := List.find?_some hk
        simp only [Int.toNat_zero, Nat.zero_add] at hp
        obtain ⟨t, ht⟩ := List.isPrefixOf_iff_prefix.mp hp
        rw [if_neg (by omega), String.ext_iff, String.toList_ofList]
        have hd : s.toList.drop k = a.toList ++ t := ht.symm
        have : s.toList.drop (k + a.length) = t := by
          rw [← List.drop_drop, hd, ← String.length_toList]; simp
        simp only [Int.zero_add, Int.toNat_natCast, this, List.append_assoc, ← hd, List.take_append_drop]
      · simp
    · simp

theorem at_zero_empty (s : String) : Fren.Str.at s 0 = "" ↔ s = "" := by
  simp only [Fren.Str.at, slice, String.ext_iff]
  rcases hs : s.toList with _ | ⟨d, rest⟩
  · simp [← String.length_toList, hs]
  · simp [← String.length_toList, hs]

end Str

impl one_character: lint::one_character for (s t : String) (i : Int) (u : String) {
  s := s,
  t := t,
  i := i,
  u := u,
  first? := Fren.Str.at s 0 == t,
  last? := Fren.Str.at s (Fren.Str.len s - 1) == t,
  slice? := Fren.Str.slice s i 1 == u,
} by
  intro s t i u h
  simp only [fren_spec] at h
  simp only [fren_spec, beq_iff_eq]
  exact ⟨Str.at_zero s t h, Str.at_last s t h, Iff.rfl⟩

impl first_empty: lint::first_empty for (s : String) {
  s := s,
  empty? := Fren.Str.at s 0 == "",
} by
  intro s _
  simp [fren_spec, Str.at_zero_empty]

impl redundant_slicing: lint::redundant_slicing for (w : Bool) (s : String) (i n : Int) (u : String) {
  whole? := w,
  s := s,
  i := i,
  n := n,
  u := u,
  fires? := Fren.Core.redundantSlicing w,
  slice? := Fren.Str.slice s i n == u,
} by
  intro w s i n u h
  simp only [fren_spec] at h
  cases w <;> simp_all [fren_spec, Fren.Core.redundantSlicing, Str.slice_whole]

impl no_effect_replace: lint::no_effect_replace for (same : Bool) (s a b u : String) {
  same? := same,
  s := s,
  a := a,
  b := b,
  u := u,
  fires? := Fren.Core.noEffectReplace same,
  replaced? := Fren.Str.replace s a b == u,
  replaced_all? := Fren.Str.replaceAll s a b == u,
} by
  intro same s a b u h
  simp only [fren_spec] at h
  cases same <;> simp_all [fren_spec, Fren.Core.noEffectReplace, Str.replace_self, Str.replaceAll_self]

impl const_is_empty: lint::const_is_empty for (c : Comparison) (b : Int) (l set : Bool) (n : Nat) {
  op := toComparison c,
  bound := b,
  left? := l,
  set? := set,
  n := n,
  fires? := (Fren.Core.constIsEmpty c b l set n).1,
  value? := (Fren.Core.constIsEmpty c b l set n).2,
} by
  intro c b l set n _
  refine ⟨toComparison c, b, l, (Fren.Core.lengthZero c b l).1, (Fren.Core.lengthZero c b l).2, ?_, ?_⟩
  all_goals cases c <;> cases l <;> cases set <;>
    simp [fren_spec, toComparison, Fren.Core.constIsEmpty, Fren.Core.lengthZero, Fren.Core.Comparison.mirror,
      Fren.Core.Comparison.compares]
  all_goals done

impl const_empty_equation: lint::const_empty_equation for (e : Bool) (n : Nat) {
  equal? := e,
  n := n,
  fires? := (Fren.Core.constEmptyEquation e n).1,
  value? := (Fren.Core.constEmptyEquation e n).2,
} by
  intro e n _
  cases e <;> simp [fren_spec, Fren.Core.constEmptyEquation] <;> omega

impl manual_pattern_char_comparison: lint::manual_pattern_char_comparison for (n : Nat) (single : Bool) {
  n_alternatives := n,
  single? := single,
  fires? := Fren.Core.manualPatternCharComparison n single,
} by
  intro n single _
  cases single <;> simp [fren_spec, Fren.Core.manualPatternCharComparison] <;> omega

-- For every character, written as a string of one.
impl class_char: lint::class_char for (c : Char) {
  c := c.toString,
  escaped? := Fren.Core.classCharText c != c.toString,
} by
  intro c _
  have inj (d : Char) : String.singleton c = String.singleton d ↔ c = d :=
    ⟨fun h => by simpa using congrArg String.toList h, fun h => h ▸ rfl⟩
  have ne : "\\".push c ≠ String.singleton c := fun h => by simpa using congrArg String.length h
  simp only [fren_spec, Fren.Core.classCharText]
  have lits : (String.singleton c = "\\" ↔ c = '\\') ∧ (String.singleton c = "]" ↔ c = ']') ∧
      (String.singleton c = "^" ↔ c = '^') ∧ (String.singleton c = "-" ↔ c = '-') :=
    ⟨inj '\\', inj ']', inj '^', inj '-'⟩
  by_cases h : c = '\\' ∨ c = ']' ∨ c = '^' ∨ c = '-' <;>
    simp_all [Fren.Str.lit, lits.1, lits.2.1, lits.2.2.1, lits.2.2.2]

impl almost_complete_range: lint::almost_complete_range for (lo hi : Int) {
  low := lo,
  high := hi,
  fires? := (Fren.Core.almostCompleteRange lo hi).1,
  whole_low := (Fren.Core.almostCompleteRange lo hi).2.1,
  whole_high := (Fren.Core.almostCompleteRange lo hi).2.2,
} by
  intro lo hi _
  simp [fren_spec, Fren.Core.almostCompleteRange, or_assoc]

/-! ## Restriction -/

-- Both front ends decide a `set_option` with `allowAttributes`.
impl allow_attributes: lint::allow_attributes for (l : LintLevel) (u : Bool) {
  requested := toLintLevel l,
  unfulfilled? := u,
  fires? := (Fren.Core.allowAttributes l u).1,
  fixed? := (Fren.Core.allowAttributes l u).2,
}

-- Both front ends decide a `_` arm with `wildcardEnumMatchArm`.
impl wildcard_enum_match_arm: lint::wildcard_enum_match_arm for (w : Bool) (n : Nat) {
  wildcard? := w,
  n_unnamed := n,
  fires? := (Fren.Core.wildcardEnumMatchArm w n).1,
  fixed? := (Fren.Core.wildcardEnumMatchArm w n).2,
} by
  intro w n _
  cases w <;> simp [fren_spec, Fren.Core.wildcardEnumMatchArm]

impl needless_raw_strings: lint::needless_raw_strings for (r b q : Bool) {
  raw? := r,
  backslash? := b,
  quote? := q,
  fires? := Fren.Core.needlessRawStrings r b q,
}

impl non_ascii_literal: lint::non_ascii_literal for (n : Nat) {
  code := n,
  fires? := (Fren.Core.nonAscii n).1,
  escapable? := (Fren.Core.nonAscii n).2,
} by
  intro n _
  simp [fren_spec, Fren.Core.nonAscii]
  omega

impl module_name_repetitions: lint::module_name_repetitions for (n m : Nat) (c : Bool) {
  n_words := n,
  n_module_words := m,
  contains? := c,
  fires? := Fren.Core.moduleNameRepetitions n m c,
} by
  intro n m c _
  cases c <;> simp [fren_spec, Fren.Core.moduleNameRepetitions] <;> omega

-- Over a `String`: `minIdentChars` takes the name with its final `?`.
tested lint::min_ident_chars: "test/ui/lints/restriction.fren", "test/cli/lints/restriction/f0785_min_ident_chars.fren"

impl absolute_paths: lint::absolute_paths for (n : Nat) {
  n_segments := n,
  fires? := Fren.Core.absolutePath n,
} by
  intro n _
  simp [fren_spec, Fren.Core.absolutePath]
  omega

-- Both front ends decide an operand with `precedenceFires`, in `opReports`.
impl precedence: lint::precedence for (o i : Fren.Core.InfixOp) (p : Bool) {
  outer := toInfixOp o,
  inner := toInfixOp i,
  parenthesized? := p,
  fires? := Fren.Core.precedenceFires o i p,
} by
  intro o i p _
  cases p
  · cases o <;> cases i <;> simp +decide [fren_spec]
  · simp [fren_spec, Fren.Core.precedenceFires]

/-! ## Copied records, settings, assumptions, binders and dots -/

-- Both front ends decide it with `unnecessaryStructInit`, on each record
-- literal, typing its receiver apart.
impl unnecessary_struct_initialization: lint::unnecessary_struct_initialization
    for (n : Nat) (o s v t : Bool) {
  n_fields := n,
  reads_own? := o,
  same? := s,
  value? := v,
  same_type? := t,
  fires? := Fren.Core.unnecessaryStructInit n o s v t,
} by
  intro n o s v t _
  cases o <;> cases s <;> cases v <;> cases t <;> simp [fren_spec, Fren.Core.unnecessaryStructInit]

trusted lint::struct_initialization_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::struct_initialization_fixed: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::empty_membership_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::empty_membership_value: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::empty_subset_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::empty_subset_value: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::literal_dot_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::literal_dot_fixed: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::literal_dot_value: "a model of an expression, checked against its fix by the refinements in its section"

-- Both front ends decide it with `unusedSettingReports`, from the settings
-- each item reads: a setting that one reads is in effect at an item.
impl unused_lint_setting: lint::unused_lint_setting for (seen e : Bool) {
  n_places := if seen then 1 else 0,
  expect? := e,
  fires? := Fren.Core.unusedLintSetting seen e,
} by
  intro seen e _
  cases seen <;> cases e <;> simp [fren_spec, Fren.Core.unusedLintSetting]

-- Both front ends decide it with `unusedAssumption`, at the component and
-- again at the end of the file, with the global expectations' reads.
impl unused_assumption: lint::unused_assumption for (n : Nat) (a m r : Bool) {
  n_mentioned := n,
  all_inputs? := a,
  mentioned? := m,
  read? := r,
  fires? := Fren.Core.unusedAssumption n a m r,
} by
  intro n a m r _
  cases a <;> cases m <;> cases r <;> simp [fren_spec, Fren.Core.unusedAssumption]

-- Both front ends count the groups with `binderGroups`.
impl unrelated_binders: lint::unrelated_binders for (n : Nat) {
  n_groups := n,
  fires? := Fren.Core.unrelatedBinders n,
} by
  intro n _
  simp only [fren_spec, Fren.Core.unrelatedBinders, decide_eq_true_eq]
  omega

-- Both front ends find the dots with `literalDotsPattern?`.
impl literal_dot_in_pattern: lint::literal_dot_in_pattern for (b a : Bool) {
  before? := b,
  after? := a,
  fires? := Fren.Core.literalDotInPattern b a,
} by
  intro b a _
  cases b <;> cases a <;> simp [fren_spec, Fren.Core.literalDotInPattern]

/-! ## Ranges of methods, Unicode normalization and trailing commas -/

-- Both front ends decide `invalid_upcast_comparisons` with `invalidUpcast`,
-- from the least value that `leastValue?` gives the method.
impl invalid_upcast_comparisons: lint::invalid_upcast_comparisons for (c : Comparison) (b m : Int) (l : Bool) {
  op := toComparison c,
  bound := b,
  lowest := m,
  left? := l,
  fires? := (Fren.Core.invalidUpcast c b m l).1,
  value? := (Fren.Core.invalidUpcast c b m l).2,
} by
  intro c b m l _
  cases c <;> cases l <;> simp [fren_spec, toComparison, Fren.Core.invalidUpcast, Fren.Core.Comparison.mirror] <;> omega

-- `unicodeNotNfc?` asks `Nfc.nfc?` for the literal's value in NFC, which is
-- `none` where Unicode 15.0 does not assign a code point of it.
impl unicode_not_nfc: lint::unicode_not_nfc for (n a e : Bool) {
  nfc? := n,
  assigned? := a,
  escapes? := e,
  fires? := (Fren.Core.unicodeNotNfc n a e).1,
  suggested? := (Fren.Core.unicodeNotNfc n a e).2,
}

-- Both front ends find the commas with `trailingCommas`, from the tokens.
impl unnecessary_trailing_comma: lint::unnecessary_trailing_comma for (b : Bool) {
  line_break? := b,
  fires? := Fren.Core.unnecessaryTrailingComma b,
}

trusted lint::invalid_upcast_written: "a model of an expression, checked by the refinements in its section"
trusted lint::invalid_upcast_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::nfc_written: "a model of a string literal, checked by the refinements in its section"
trusted lint::nfc_fixed: "a model of a string literal, checked by the refinements in its section"
trusted lint::trailing_comma_written: "a model of an expression, checked by the refinements in its section"
trusted lint::trailing_comma_fixed: "a model of an expression, checked by the refinements in its section"

-- The models of the expressions that the refinements of `match_like_membership`,
-- `is_equality`, `irrefutable_is`, `chainable_comparison`, and of `int_plus_one`
-- and `contradictory_comparisons` in chains, compare.
-- keep-sorted start
trusted lint::chainable_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::chainable_written: "a model of an expression, checked by the refinements in its section"
trusted lint::contradictory_chain_value: "a model of an expression, checked by the refinements in its section"
trusted lint::contradictory_chain_written: "a model of an expression, checked by the refinements in its section"
trusted lint::int_plus_one_chain_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::int_plus_one_chain_written: "a model of an expression, checked by the refinements in its section"
trusted lint::irrefutable_is_value: "a model of an expression, checked by the refinements in its section"
trusted lint::irrefutable_is_written: "a model of an expression, checked by the refinements in its section"
trusted lint::is_equality_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::is_equality_written: "a model of an expression, checked by the refinements in its section"
trusted lint::membership_test_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::membership_test_written: "a model of an expression, checked by the refinements in its section"
-- keep-sorted end

/-! ## Pedantic lints of expressions, matches, records and literals -/

def toBoolRule : Fren.Core.BoolRule → lint.BoolRule
  | .absorption => .Absorption
  | .contradiction => .Contradiction
  | .excludedMiddle => .ExcludedMiddle

impl overly_complex_bool_expr: lint::overly_complex_bool_expr for (c a n s : Bool) {
  conj? := c,
  absorbs? := a,
  negates? := n,
  simpler_negation? := s,
  fires? := (Fren.Core.overlyComplexBool c a n s).1,
  kind := toBoolRule (Fren.Core.overlyComplexBool c a n s).2,
} by
  intro c a n s _
  cases c <;> cases a <;> cases n <;> cases s <;> simp [fren_spec, Fren.Core.overlyComplexBool, toBoolRule]

impl branches_sharing_code: lint::branches_sharing_code for (o l r n : Bool) {
  same_op? := o,
  shared_left? := l,
  shared_right? := r,
  nonlinear? := n,
  fires? := Fren.Core.branchesSharingCode o l r n,
} by
  intro o l r n _
  cases o <;> cases l <;> cases r <;> cases n <;> simp [fren_spec, Fren.Core.branchesSharingCode]

impl needless_raw_string_hashes: lint::needless_raw_string_hashes for (h : Nat) (l : Int) {
  hashes := h,
  longest := l,
  fires? := (Fren.Core.needlessRawHashes h l).1,
  fewest := (Fren.Core.needlessRawHashes h l).2,
} by
  intro h l _
  simp [fren_spec, Fren.Core.needlessRawHashes]

impl single_match_else: lint::single_match_else for (n : Nat) (v w o : Bool) {
  n_arms := n,
  one_variant? := v,
  wildcard? := w,
  other? := o,
  fires? := Fren.Core.singleMatchElse n v w o,
} by
  intro n v w o _
  cases v <;> cases w <;> cases o <;> simp [fren_spec, Fren.Core.singleMatchElse] <;> omega

impl inconsistent_struct_constructor: lint::inconsistent_struct_constructor for (b : Bool) {
  in_order? := b,
  fires? := Fren.Core.inconsistentStructConstructor b,
} by
  intro b _
  cases b <;> simp [fren_spec, Fren.Core.inconsistentStructConstructor]

-- Decided by the functions of `enum_variant_names`.
impl struct_field_names: lint::struct_field_names for (n : Nat) (f l : Bool) {
  n_fields := n,
  shared_first? := f,
  shared_last? := l,
  fires? := Fren.Core.enumVariantNames n f l,
} by
  intro n f l _
  cases f <;> cases l <;> simp [fren_spec, Fren.Core.enumVariantNames] <;> omega

impl field_has_record_name: lint::field_has_record_name for (n r : Nat) (c : Bool) {
  n_words := n,
  n_record_words := r,
  contains? := c,
  fires? := Fren.Core.variantHasEnumName n r c,
} by
  intro n r c _
  cases c <;> simp [fren_spec, Fren.Core.variantHasEnumName] <;> omega

impl struct_excessive_bools: lint::struct_excessive_bools for (n : Nat) {
  n_bools := n,
  fires? := Fren.Core.structExcessiveBools n,
} by
  intro n _
  simp [fren_spec, Fren.Core.structExcessiveBools]
  omega

impl fn_params_excessive_bools: lint::fn_params_excessive_bools for (n : Nat) {
  n_bools := n,
  fires? := Fren.Core.fnParamsExcessiveBools n,
} by
  intro n _
  simp [fren_spec, Fren.Core.fnParamsExcessiveBools]
  omega

trusted lint::absorption_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::absorption_fixed: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::contradiction_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::contradiction_fixed: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::excluded_middle_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::excluded_middle_fixed: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::branches_sharing_code_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::branches_sharing_code_fixed: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::raw_hashes_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::raw_hashes_fixed: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::single_match_else_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::single_match_else_fixed: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::inconsistent_struct_constructor_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::inconsistent_struct_constructor_fixed: "a model of an expression, checked against its fix by the refinements in its section"

/-! ## Literals, the order of members, and functions applied once -/

-- `zeroPrefixed` reads the literal's characters, and `dropLeadingZeros`
-- writes the fix; the spec states the same with patterns, which the tests
-- check against them.
tested lint::zero_prefixed_literal: "test/ui/lints/literals.fren", "test/cli/lints/complexity/f0758_zero_prefixed_literal.fren",
  "test/cli/fix/literals.fren"

-- Both front ends find the first member out of order with
-- `firstOutOfOrder?`, which asks `outOfOrder` of each member and the one
-- before it.
impl arbitrary_source_item_ordering: lint::arbitrary_source_item_ordering for (a b : Fren.Core.MemberKind) {
  first := toMemberKind a,
  second := toMemberKind b,
  fires? := Fren.Core.outOfOrder a b,
}

-- `memberOrderFix?` asks `mentionKept` of each mention.
impl mention_kept: lint::mention_kept for (a b : Fren.Core.MemberKind) (e : Bool) {
  mentioner := toMemberKind a,
  mentioned := toMemberKind b,
  earlier? := e,
  kept? := Fren.Core.mentionKept a b e,
}

impl single_call_fn: lint::single_call_fn for (p d : Bool) (n : Nat) {
  pub? := p,
  defined? := d,
  n_uses := n,
  fires? := Fren.Core.singleCallFn d p n,
} by
  intro p d n _
  cases p <;> cases d <;> rcases n with _ | _ | n <;> simp [fren_spec, Fren.Core.singleCallFn] <;> omega

trusted lint::zero_prefixed_written: "a model of an expression, checked by the refinements in its section"
trusted lint::zero_prefixed_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::member_order_written: "a model of a component, checked by the refinements in its section"
trusted lint::member_order_fixed: "a model of a component, checked by the refinements in its section"


/-! ## Cardinality, ordered enumerations and newtypes -/

-- Both front ends decide these in `opReports`, the variants and newtypes
-- from what each elaborator records of them (`Fren.Core.NodeFact`). Where
-- a model's inputs are finite, `decide` proves the implementation over all
-- of them; a set of positions or operands is given by one `Bool` for each.

instance : Fren.Finite lint.PairNegation where
  all := [⟨.P, .P, false⟩, ⟨.P, .P, true⟩, ⟨.P, .Q, false⟩, ⟨.P, .Q, true⟩, ⟨.P, .R, false⟩, ⟨.P, .R, true⟩, ⟨.P, .S, false⟩, ⟨.P, .S, true⟩, ⟨.Q, .P, false⟩, ⟨.Q, .P, true⟩, ⟨.Q, .Q, false⟩, ⟨.Q, .Q, true⟩, ⟨.Q, .R, false⟩, ⟨.Q, .R, true⟩, ⟨.Q, .S, false⟩, ⟨.Q, .S, true⟩, ⟨.R, .P, false⟩, ⟨.R, .P, true⟩, ⟨.R, .Q, false⟩, ⟨.R, .Q, true⟩, ⟨.R, .R, false⟩, ⟨.R, .R, true⟩, ⟨.R, .S, false⟩, ⟨.R, .S, true⟩, ⟨.S, .P, false⟩, ⟨.S, .P, true⟩, ⟨.S, .Q, false⟩, ⟨.S, .Q, true⟩, ⟨.S, .R, false⟩, ⟨.S, .R, true⟩, ⟨.S, .S, false⟩, ⟨.S, .S, true⟩]
  complete := by intro ⟨x, y, o⟩; cases x <;> cases y <;> cases o <;> decide

instance : Fren.Finite lint.Argument where
  all := [.Literal false, .Literal true, .Written .P, .Written .Q, .Written .R, .Written .S]
  complete := by intro a; cases a with | Literal b => cases b <;> decide | Written x => cases x <;> decide

instance : Fren.Finite lint.Inner where
  all := [.FieldOf .Ms, .FieldOf .Bytes, .Typed, .Untyped]
  complete := by intro a; cases a with | FieldOf t => cases t <;> decide | _ => decide

instance : Fren.Finite lint.Roundtrip where
  all := (Fren.Finite.all : List lint.Inner).flatMap fun e =>
    [.Built .Ms e, .Built .Bytes e, .Read .Ms e, .Read .Bytes e]
  complete := by
    intro r
    cases r with
    | Built t e => cases t <;> cases e with | FieldOf u => cases u <;> decide | _ => decide
    | Read t e => cases t <;> cases e with | FieldOf u => cases u <;> decide | _ => decide

theorem any_finite {α : Type} [Fren.Finite α] [DecidableEq α] (l : List α) (f : α → Bool) :
    l.any f = (Fren.Finite.all : List α).any fun x => decide (x ∈ l) && f x := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨x, h, hf⟩ => ⟨x, Fren.Finite.complete x, h, hf⟩, fun ⟨x, _, h, hf⟩ => ⟨x, h, hf⟩⟩

theorem all_finite {α : Type} [Fren.Finite α] [DecidableEq α] (l : List α) (f : α → Bool) :
    l.all f = (Fren.Finite.all : List α).all fun x => !decide (x ∈ l) || f x := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  exact ⟨fun h x _ => (Classical.em (x ∈ l)).elim (fun hx => Or.inr (h x hx)) Or.inl,
    fun h x hx => ((h x (Fren.Finite.complete x)).resolve_left (by simpa using hx))⟩

theorem mem_operands (ps : List lint.PairNegation) (x : lint.Operand) :
    decide (x ∈ ps.flatMap fun p => [p.first, p.second])
      = ps.any fun p => p.first == x || p.second == x := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, List.any_eq_true,
    Bool.or_eq_true, beq_iff_eq]
  exact ⟨fun ⟨p, h, e⟩ => ⟨p, h, e.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)⟩,
    fun ⟨p, h, e⟩ => ⟨p, h, e.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)⟩⟩

theorem contains_eq {α : Type} [DecidableEq α] (l : List α) (x : α) : l.contains x = decide (x ∈ l) := by
  simp

impl manual_at_most_one: lint::manual_at_most_one for (ps : List lint.PairNegation) (ds : List lint.Operand) {
  pairs := Fren.FinSet.ofList ps,
  disjunction := Fren.FinSet.ofList ds,
  fires? := (Fren.Core.manualAtMostOne lint.PairNegation.first lint.PairNegation.second lint.PairNegation.«obligation?» ps ds).1,
  exactly? := (Fren.Core.manualAtMostOne lint.PairNegation.first lint.PairNegation.second lint.PairNegation.«obligation?» ps ds).2,
} by
  intro ps ds _
  generalize hm : (fun p => decide (p ∈ ps)) = m
  generalize hd : (fun x => decide (x ∈ ds)) = d
  have hm' : ∀ p, p ∈ ps ↔ m p = true := fun p => by rw [← hm]; simp
  have hd' : ∀ x, x ∈ ds ↔ d x = true := fun x => by rw [← hd]; simp
  have hdn : ds = [] ↔ ((Fren.Finite.all : List lint.Operand).all fun x => !decide (x ∈ ds)) = true := by
    simp only [List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨fun h x _ => by simp [h], fun h => List.eq_nil_iff_forall_not_mem.mpr fun x => h x (Fren.Finite.complete x)⟩
  simp only [fren_spec]
  simp only [Fren.Core.manualAtMostOne, FinSet.mem_ofList, hm', hd']
  simp only [any_finite (ps.flatMap fun p => [p.first, p.second]), all_finite (ps.flatMap fun p => [p.first, p.second]),
    any_finite ps, all_finite ps, all_finite ds, mem_operands, contains_eq, any_finite ds]
  have opBeq : ∀ a b : lint.Operand, (a == b) = decide (a = b) := by decide
  have opBne : ∀ a b : lint.Operand, (a != b) = !decide (a = b) := by decide
  try simp only [FinSet.ofList_eq_empty, hdn]
  have hmx : ∀ p, decide (p ∈ ps) = m p := fun p => congrFun hm p
  have hdx : ∀ x, decide (x ∈ ds) = d x := fun x => congrFun hd x
  try simp only [hmx, hdx]
  have hde : FinSet.ofList ds = ∅ ↔ ((Fren.Finite.all : List lint.Operand).all fun x => !d x) = true := by
    rw [FinSet.ofList_eq_empty, hdn]; simp only [hdx]
  simp only [Fren.Finite.all, List.any_cons, List.all_cons, List.any_nil, List.all_nil, opBeq, opBne, ne_eq,
    reduceCtorEq, not_false_eq_true, decide_true, decide_false, Bool.true_and, Bool.and_true,
    Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or, Bool.true_or, Bool.or_true, Bool.not_true, Bool.not_false]
  try simp (config := { decide := true }) only []
  rw [hde]
  simp only [Fren.Finite.all, List.all_cons, List.all_nil, Bool.and_true]
  bv_decide

def toCardinalityFix : Bool × Bool → lint.CardinalityFix
  | (false, _) => .Unchanged
  | (true, true) => .Argument
  | (true, false) => .True

impl nonminimal_cardinality: lint::nonminimal_cardinality for (e : Bool) (args : List Bool) {
  exactly? := e,
  args := Fren.Seq.ofList args,
  fix := toCardinalityFix (Fren.Core.nonminimalCardinality e args.length),
} by
  intro e args _
  have h' : ((args.length : Int) = 1) ↔ args.length = 1 := by omega
  cases e <;> by_cases h : args.length = 1 <;>
    simp [fren_spec, Fren.Core.nonminimalCardinality, toCardinalityFix, h, h']

/-- The operands whose `Bool` is `true`, in order. -/
def chosenOperands (p q r s : Bool) : List lint.Operand :=
  ([(lint.Operand.P, p), (.Q, q), (.R, r), (.S, s)].filter (·.2)).map (·.1)

def argOperand : lint.Argument → Option lint.Operand
  | .Written x => some x
  | .Literal _ => none

impl eq_op_cardinality: lint::eq_op_cardinality for (p q r s : Bool) (a : lint.Argument) {
  earlier := Fren.FinSet.ofList (chosenOperands p q r s),
  argument := a,
  fires? := Fren.Core.eqOpCardinality (chosenOperands p q r s) (argOperand a),
}

def posIdx : lint.Position → Nat
  | .V0 => 0
  | .V1 => 1
  | .V2 => 2
  | .V3 => 3
  | .V4 => 4

def ofPosIdx : Nat → lint.Position
  | 0 => .V0
  | 1 => .V1
  | 2 => .V2
  | 3 => .V3
  | _ => .V4

/-- The positions whose `Bool` is `true`, in order. -/
def chosenPositions (b0 b1 b2 b3 b4 : Bool) : List lint.Position :=
  ([(lint.Position.V0, b0), (.V1, b1), (.V2, b2), (.V3, b3), (.V4, b4)].filter (·.2)).map (·.1)

def ofLintComparison : lint.Comparison → Comparison
  | .Eq => .eq
  | .Ne => .ne
  | .Lt => .lt
  | .Le => .le
  | .Gt => .gt
  | .Ge => .ge

def toOrderingFix : Option (Comparison × Nat) → lint.OrderingFix
  | none => .Unchanged
  | some (c, k) => .Compare (toComparison c) (ofPosIdx k)

impl manual_ordering: lint::manual_ordering for (l : lint.Position) (b0 b1 b2 b3 b4 g : Bool) {
  named := ⟨b0, b1, b2, b3, b4⟩,
  last := l,
  negated? := g,
  fix := toOrderingFix (Fren.Core.manualOrdering (posIdx l + 1) ((chosenPositions b0 b1 b2 b3 b4).map posIdx) g),
} by
  intro l b0 b1 b2 b3 b4 g
  cases l <;> cases g <;> revert b0 b1 b2 b3 b4 <;> decide

def toAbsurdValue : Bool × Bool → lint.AbsurdValue
  | (true, true) => .AlwaysTrue
  | (true, false) => .AlwaysFalse
  | (false, _) => .NotFixed

impl absurd_ordered: lint::absurd_ordered for (c : lint.Comparison) (v l : lint.Position) (r : Bool) {
  op := c,
  variant := v,
  last := l,
  right? := r,
  value := toAbsurdValue (Fren.Core.absurdOrdered (ofLintComparison c) (posIdx v) (posIdx l + 1) r),
}

def toMinMaxFix : Option Bool → lint.MinMaxFix
  | none => .Unchanged
  | some true => .Argument
  | some false => .Receiver

impl unnecessary_min_or_max: lint::unnecessary_min_or_max for (m : Bool) (a l : lint.Position) {
  max? := m,
  argument := a,
  last := l,
  fix := toMinMaxFix (Fren.Core.unnecessaryMinOrMax m (posIdx a) (posIdx l + 1)),
}

def ofLintInner : lint.Inner → Fren.Core.RoundtripInner lint.Newtype
  | .FieldOf t => .fieldOf t
  | .Typed => .typed
  | .Untyped => .untyped

def ofLintRoundtrip : lint.Roundtrip → Fren.Core.Roundtrip lint.Newtype
  | .Built t e => .built t (ofLintInner e)
  | .Read t e => .read t (ofLintInner e)

def toRoundtripFix : Fren.Core.RoundtripFix → lint.RoundtripFix
  | .unchanged => .Unchanged
  | .reported => .Reported
  | .fixed => .Fixed

impl redundant_newtype_roundtrip: lint::redundant_newtype_roundtrip for (r : lint.Roundtrip) {
  shape := r,
  fix := toRoundtripFix (Fren.Core.redundantNewtypeRoundtrip (ofLintRoundtrip r)),
}

-- keep-sorted start
trusted lint::eq_op_cardinality_value: "a model of an expression, checked by the refinements in its section"
trusted lint::eq_op_cardinality_written: "a model of an expression, checked by the refinements in its section"
trusted lint::manual_at_most_one_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::manual_at_most_one_guarded: "a test that the lint does not fire, checked by its `deny`"
trusted lint::manual_at_most_one_written: "a model of an expression, checked by the refinements in its section"
trusted lint::manual_ordering_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::manual_ordering_written: "a model of an expression, checked by the refinements in its section"
trusted lint::min_or_max_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::min_or_max_written: "a model of an expression, checked by the refinements in its section"
trusted lint::nonminimal_cardinality_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::nonminimal_cardinality_written: "a model of an expression, checked by the refinements in its section"
trusted lint::roundtrip_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::roundtrip_written: "a model of an expression, checked by the refinements in its section"
-- keep-sorted end

/-! ## Record updates and cover goals -/

-- Both front ends count the copies of the value with the most, of the
-- literal's own record, as the elaborator types it.
impl manual_record_update: lint::manual_record_update for (f c : Nat) {
  n_fields := f,
  n_copied := c,
  fires? := Fren.Core.manualRecordUpdate f c,
} by
  intro f c _
  simp [fren_spec, Fren.Core.manualRecordUpdate] <;> omega

impl field_copy: lint::field_copy for (f v b : String) (o : Bool) {
  path? := Fren.Core.pathText b,
  copy? := v == b ++ "." ++ f,
  others? := o,
  fires? := Fren.Core.fieldCopy f v b o,
} by
  intro f v b o _
  simp [fren_spec, Fren.Core.fieldCopy]

impl needless_update: lint::needless_update for (f g : Nat) {
  n_fields := f,
  n_given := g,
  fires? := Fren.Core.needlessUpdate f g,
} by
  intro f g _
  simp [fren_spec, Fren.Core.needlessUpdate]

-- What a goal restates is passed as the kind and name of the first
-- assumption or guarantee written the same; only whether there is one
-- decides whether the lint fires.
impl trivial_cover: lint::trivial_cover for (t r : Bool) {
  trigger? := t,
  restates? := r,
  fires? := (Fren.Core.trivialCover t (if r then some ("assumption", .anonymous) else none)).isSome,
} by
  intro t r _
  cases t <;> cases r <;> simp [fren_spec, Fren.Core.trivialCover]

trusted lint::field_copy_written: "a model of record updates, checked by the refinements in its section"
trusted lint::field_copy_fixed: "a model of record updates, checked by the refinements in its section"
trusted lint::manual_record_update_written: "a model of a record literal, checked by the refinements in its section"
trusted lint::manual_record_update_fixed: "a model of a record literal, checked by the refinements in its section"
trusted lint::needless_update_written: "a model of a record update, checked by the refinements in its section"
trusted lint::needless_update_fixed: "a model of a record update, checked by the refinements in its section"

end Fren.Impls
