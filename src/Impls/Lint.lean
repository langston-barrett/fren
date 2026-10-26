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

impl membership_chain: lint::membership_chain for (n : Nat) (same later pats : Bool) {
  n := n,
  same_left? := same,
  later_indexes? := later,
  patterns? := pats,
  fires? := Fren.Core.membershipChainFires n same later pats,
} by
  intro n same later pats _
  cases same <;> cases later <;> cases pats <;> simp [fren_spec, Fren.Core.membershipChainFires] <;> omega

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
  simp only [fren_spec, Fren.Core.matchMembership]
  cases w <;> cases wt <;> cases d <;> cases ff <;> cases ef <;> cases et <;> by_cases h : f < t <;> simp [h] <;> omega

impl wildcard_single_variant: lint::wildcard_single_variant for (n : Nat) {
  n_matched := n,
  fires? := Fren.Core.wildcardSingle n,
} by
  intro n _
  simp [fren_spec, Fren.Core.wildcardSingle]
  omega

-- Both front ends decide `is_equality` and `irrefutable_is` with
-- `isEquality` and `irrefutableIs`, where they elaborate the test.
impl is_equality: lint::is_equality for (n : Nat) (e i : Bool) {
  n_alternatives := n,
  equatable? := e,
  irrefutable? := i,
  fires? := Fren.Core.isEquality n e i,
} by
  intro n e i _
  cases e <;> cases i <;> simp [fren_spec, Fren.Core.isEquality] <;> omega

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
  ⟨[.add, .sub, .mul, .concat, .union, .minus, .div], by intro x; cases x <;> simp⟩

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
  | .div => .Div

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

/-! ### Pattern tests written out -/

def toBound : lint.Bound → Option Int
  | .Open => none
  | .At k => some k

/-- An alternative of the model as `manual_pattern_test` reads one
(`lint::Alt`). -/
def toPatAlt : lint.Alt → Fren.Core.PatAlt
  | .Ints l h => .ints (toBound l) (toBound h)
  | .Text s => .str s
  | .Variant v => .variant v

theorem boundBelow_eq (h l : lint.Bound) : Fren.Core.boundBelow (toBound h) (toBound l) = lint.bound_below? h l := by
  cases h <;> cases l <;> simp [fren_spec, toBound, Fren.Core.boundBelow, lint.bound_below?, lint.Bound.At.x0]

theorem disjoint_eq (a b : lint.Alt) : (toPatAlt a).disjoint (toPatAlt b) = lint.alts_disjoint? a b := by
  rw [Bool.eq_iff_iff]
  cases a <;> cases b <;> simp only [toPatAlt, Fren.Core.PatAlt.disjoint, boundBelow_eq] <;>
    simp [fren_spec, lint.alts_disjoint?, lint.bound_below?, lint.Alt.Ints.x0, lint.Alt.Ints.x1, lint.Alt.Text.x0,
      lint.Alt.Variant.x0, lint.Bound.At.x0]

theorem pairwiseDisjoint_iff (l : List Fren.Core.PatAlt) :
    Fren.Core.pairwiseDisjoint l = true ↔ l.Pairwise (fun a b => a.disjoint b = true) := by
  induction l with
  | nil => simp [Fren.Core.pairwiseDisjoint]
  | cons a as ih => simp [Fren.Core.pairwiseDisjoint, ih, List.pairwise_cons, List.all_eq_true]

-- The alternatives are pairwise disjoint, by their positions in the model's
-- sequence.
theorem pairwise_nth (l : List lint.Alt) :
    Fren.Core.pairwiseDisjoint (l.map toPatAlt) = true ↔
      ∀ i j : Int, 0 ≤ i → i < j → j < (Fren.Seq.ofList l).len →
        lint.alts_disjoint? ((Fren.Seq.ofList l).nth i) ((Fren.Seq.ofList l).nth j) = true := by
  rw [pairwiseDisjoint_iff, List.pairwise_map, List.pairwise_iff_getElem]
  simp only [disjoint_eq, Fren.Seq.len_eq, Fren.Seq.toList_ofList]
  constructor
  · intro h i j hi hij hj
    rw [Fren.Seq.nth_of_lt _ _ hi (by simp; omega), Fren.Seq.nth_of_lt _ _ (by omega) (by simp; omega)]
    simp only [Fren.Seq.toList_ofList]
    exact h _ _ _ _ (by omega)
  · intro h i j hi hj hij
    have := h i j (by omega) (by omega) (by omega)
    rwa [Fren.Seq.nth_of_lt _ _ (by omega) (by simp; omega), Fren.Seq.nth_of_lt _ _ (by omega) (by simp; omega)] at this

theorem manualPatternTest_iff (l : List lint.Alt) (n e : Nat) (c : Bool) :
    Fren.Core.manualPatternTest (l.map toPatAlt) n e c = true ↔
      (((n : Int) ≥ 2 ∧ (e : Int) ≥ 1) ∧ ¬c = true) ∧
        ∀ i j : Int, 0 ≤ i → i < j → j < (Fren.Seq.ofList l).len →
          lint.alts_disjoint? ((Fren.Seq.ofList l).nth i) ((Fren.Seq.ofList l).nth j) = true := by
  rw [← pairwise_nth]
  simp only [Fren.Core.manualPatternTest, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  cases c <;> simp <;> omega

-- The spec's quantifiers over positions, expanded as Fren expands them, are
-- the quantifier over every position of the sequence, which has at most
-- eight.
impl manual_pattern_test: lint::manual_pattern_test for (l : List lint.Alt) (n e : Nat) (c : Bool) {
  alts := Fren.Seq.ofList l,
  n_operands := n,
  n_equations := e,
  chain? := c,
  fires? := Fren.Core.manualPatternTest (l.map toPatAlt) n e c,
} by
  intro l n e c hs
  unfold lint.manual_pattern_test.ensures lint.manual_pattern_test.ensure.rule
  rw [manualPatternTest_iff]
  refine and_congr_right fun _ => ?_
  have _hl : (Fren.Seq.ofList l).len ≤ 8 := hs
  constructor
  · intro h
    and_intros <;> exact fun hc => h _ _ (by decide) hc.1 hc.2
  · intro E i j hi hij hj
    rcases E with
      ⟨⟨⟨⟨⟨⟨_, h01⟩, ⟨h02, h03⟩⟩, ⟨⟨h04, h05⟩, ⟨h06, h07⟩⟩⟩,
      ⟨⟨⟨_, _⟩, ⟨h12, h13⟩⟩, ⟨⟨h14, h15⟩, ⟨h16, h17⟩⟩⟩⟩,
      ⟨⟨⟨⟨_, _⟩, ⟨_, h23⟩⟩, ⟨⟨h24, h25⟩, ⟨h26, h27⟩⟩⟩,
      ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨h34, h35⟩, ⟨h36, h37⟩⟩⟩⟩⟩,
      ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, h45⟩, ⟨h46, h47⟩⟩⟩,
      ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨h56, h57⟩⟩⟩⟩,
      ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, h67⟩⟩⟩,
      ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩⟩⟩⟩
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · exact h01 ⟨by decide, hj⟩
    · exact h02 ⟨by decide, hj⟩
    · exact h03 ⟨by decide, hj⟩
    · exact h04 ⟨by decide, hj⟩
    · exact h05 ⟨by decide, hj⟩
    · exact h06 ⟨by decide, hj⟩
    · exact h07 ⟨by decide, hj⟩
    · omega
    · omega
    · exact h12 ⟨by decide, hj⟩
    · exact h13 ⟨by decide, hj⟩
    · exact h14 ⟨by decide, hj⟩
    · exact h15 ⟨by decide, hj⟩
    · exact h16 ⟨by decide, hj⟩
    · exact h17 ⟨by decide, hj⟩
    · omega
    · omega
    · omega
    · exact h23 ⟨by decide, hj⟩
    · exact h24 ⟨by decide, hj⟩
    · exact h25 ⟨by decide, hj⟩
    · exact h26 ⟨by decide, hj⟩
    · exact h27 ⟨by decide, hj⟩
    · omega
    · omega
    · omega
    · omega
    · exact h34 ⟨by decide, hj⟩
    · exact h35 ⟨by decide, hj⟩
    · exact h36 ⟨by decide, hj⟩
    · exact h37 ⟨by decide, hj⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact h45 ⟨by decide, hj⟩
    · exact h46 ⟨by decide, hj⟩
    · exact h47 ⟨by decide, hj⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact h56 ⟨by decide, hj⟩
    · exact h57 ⟨by decide, hj⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact h67 ⟨by decide, hj⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega

-- The models of the expressions that the refinements of `match_like_membership`,
-- `is_equality`, `manual_pattern_test`, `irrefutable_is`, `chainable_comparison`, and of `int_plus_one`
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
trusted lint::manual_pattern_test_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::manual_pattern_test_written: "a model of an expression, checked by the refinements in its section"
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
-- of them; a set of operands, or the variants a test names, is given by one
-- `Bool` for each.

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

-- `manual_at_most_one`, over every list of conjuncts: the code's reading
-- of the conjuncts is characterised with the spec's `named?` and
-- `pair_negated?`, and the quantifiers over the four operands expanded as
-- Fren expands them.
theorem exOp (P : lint.Operand → Prop) : (∃ x, P x) ↔ (P .P ∨ P .Q) ∨ (P .R ∨ P .S) := by
  constructor
  · rintro ⟨x, h⟩; cases x <;> simp_all
  · rintro ((h | h) | (h | h)) <;> exact ⟨_, h⟩

theorem allOp (P : lint.Operand → Prop) : (∀ x, P x) ↔ (P .P ∧ P .Q) ∧ (P .R ∧ P .S) := by
  constructor
  · intro h; exact ⟨⟨h _, h _⟩, ⟨h _, h _⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ x; cases x <;> assumption

theorem named_iff (ps : FinSet lint.PairNegation) (x : lint.Operand) :
    lint.named? ps x = true ↔ ∃ y, lint.pair_negated? ps x y = true ∨ lint.pair_negated? ps y x = true := by
  rw [exOp]; simp only [lint.named?, decide_eq_true_eq]

theorem pair_negated_iff (ps : List lint.PairNegation) (x y : lint.Operand) :
    lint.pair_negated? (FinSet.ofList ps) x y = true ↔ ∃ p ∈ ps, p.first = x ∧ p.second = y := by
  simp only [lint.pair_negated?, decide_eq_true_eq, FinSet.mem_ofList]
  constructor
  · rintro (h | h) <;> exact ⟨_, h, rfl, rfl⟩
  · rintro ⟨⟨a, b, o⟩, h, rfl, rfl⟩; cases o <;> simp_all

-- The conjuncts' operands, as the lint reads them.
theorem mem_ops (ps : List lint.PairNegation) (x : lint.Operand) :
    x ∈ ps.flatMap (fun p => [p.first, p.second]) ↔ lint.named? (FinSet.ofList ps) x = true := by
  simp only [named_iff, pair_negated_iff, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨p, h, e | e⟩
    · exact ⟨p.second, Or.inl ⟨p, h, e.symm, rfl⟩⟩
    · exact ⟨p.first, Or.inr ⟨p, h, rfl, e.symm⟩⟩
  · rintro ⟨y, ⟨p, h, e1, _⟩ | ⟨p, h, _, e2⟩⟩
    · exact ⟨p, h, Or.inl e1.symm⟩
    · exact ⟨p, h, Or.inr e2.symm⟩

theorem negated_iff (ps : List lint.PairNegation) (x y : lint.Operand) :
    (ps.any fun p => p.first == x && p.second == y) = true ↔ lint.pair_negated? (FinSet.ofList ps) x y = true := by
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, lint.pair_negated?, decide_eq_true_eq, FinSet.mem_ofList]
  constructor
  · rintro ⟨⟨a, b, o⟩, h, rfl, rfl⟩; cases o <;> simp_all
  · rintro (h | h) <;> exact ⟨_, h, rfl, rfl⟩

section
variable (ps : List lint.PairNegation) (ds : List lint.Operand)

local notation "N" => fun x => lint.named? (FinSet.ofList ps) x = true
local notation "G" => fun x y => lint.pair_negated? (FinSet.ofList ps) x y = true

theorem mam_fst :
    (Fren.Core.manualAtMostOne lint.PairNegation.first lint.PairNegation.second lint.PairNegation.«obligation?» ps ds).1 = true ↔
      (((∃ x y z, ((((x ≠ y ∧ x ≠ z) ∧ y ≠ z) ∧ lint.named? (FinSet.ofList ps) x = true)
          ∧ lint.named? (FinSet.ofList ps) y = true) ∧ lint.named? (FinSet.ofList ps) z = true)
        ∧ (∀ x, ¬ lint.pair_negated? (FinSet.ofList ps) x x = true))
        ∧ (∀ x y, (x ≠ y ∧ lint.named? (FinSet.ofList ps) x = true) ∧ lint.named? (FinSet.ofList ps) y = true →
            lint.pair_negated? (FinSet.ofList ps) x y = true ∨ lint.pair_negated? (FinSet.ofList ps) y x = true))
        ∧ ¬ ∃ x y, (⟨x, y, true⟩ : lint.PairNegation) ∈ FinSet.ofList ps := by
  simp only [Fren.Core.manualAtMostOne, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, List.all_eq_true,
    bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq, ← mem_ops ps, ← negated_iff ps,
    List.any_eq_false, FinSet.mem_ofList]
  refine and_congr (and_congr (and_congr ?_ ?_) ?_) ?_
  · constructor
    · rintro ⟨x, hx, y, hy, z, hz, h⟩
      exact ⟨x, y, z, ⟨⟨⟨⟨h.1.1, h.1.2⟩, h.2⟩, hx⟩, hy⟩, hz⟩
    · rintro ⟨x, y, z, ⟨⟨⟨⟨h1, h2⟩, h3⟩, hx⟩, hy⟩, hz⟩
      exact ⟨x, hx, y, hy, z, hz, by simp [h1, h2, h3]⟩
  · constructor
    · rintro h x ⟨p, hp, e1, e2⟩; exact h p hp (e1.trans e2.symm)
    · intro h p hp e; exact h p.first ⟨p, hp, rfl, e.symm⟩
  · constructor
    · rintro h x y ⟨⟨hne, hx⟩, hy⟩
      rcases h x hx y hy with (e | g) | g
      · exact absurd e hne
      · exact Or.inl g
      · exact Or.inr g
    · intro h x hx y hy
      by_cases e : x = y
      · exact Or.inl (Or.inl e)
      · rcases h x y ⟨⟨e, hx⟩, hy⟩ with g | g
        · exact Or.inl (Or.inr g)
        · exact Or.inr g
  · constructor
    · rintro h ⟨x, y, hm⟩; exact absurd rfl (h _ hm)
    · intro h p hp; cases e : p.«obligation?»
      · simp
      · exact absurd ⟨p.first, p.second, by cases p; simp_all⟩ h

theorem mam_snd :
    (Fren.Core.manualAtMostOne lint.PairNegation.first lint.PairNegation.second lint.PairNegation.«obligation?» ps ds).2 = true ↔
      ¬ FinSet.ofList ds = ∅ ∧ ∀ x, (x ∈ FinSet.ofList ds ↔ lint.named? (FinSet.ofList ps) x = true) := by
  simp only [Fren.Core.manualAtMostOne, Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.contains_iff_mem,
    ← mem_ops ps, FinSet.mem_ofList, FinSet.ofList_eq_empty, and_true]
  constructor
  · rintro ⟨⟨⟨x, hx⟩, h1⟩, h2⟩
    exact ⟨List.ne_nil_of_mem hx, fun y => ⟨h1 y, h2 y⟩⟩
  · rintro ⟨hne, h⟩
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil ds hne
    exact ⟨⟨⟨x, hx⟩, fun y hy => (h y).mp hy⟩, fun y hy => (h y).mpr hy⟩
end

impl manual_at_most_one: lint::manual_at_most_one for (ps : List lint.PairNegation) (ds : List lint.Operand) {
  pairs := Fren.FinSet.ofList ps,
  disjunction := Fren.FinSet.ofList ds,
  fires? := (Fren.Core.manualAtMostOne lint.PairNegation.first lint.PairNegation.second lint.PairNegation.«obligation?» ps ds).1,
  exactly? := (Fren.Core.manualAtMostOne lint.PairNegation.first lint.PairNegation.second lint.PairNegation.«obligation?» ps ds).2,
} by
  intro ps ds _
  unfold lint.manual_at_most_one.ensures lint.manual_at_most_one.ensure.rule lint.manual_at_most_one.ensure.fix
  rw [mam_fst, mam_snd]
  simp only [exOp, allOp, and_self]


-- `manual_at_most_one_any`, the precise rule, over every list of conjuncts
-- and every number of operands: the code's reading of the conjuncts is
-- characterised with the spec's `written_named?` and `written_negated?`, and
-- each `forall` of the rule is a `∀`.
theorem wnamed_iff (ps : List lint.WrittenNegation) (x : String) :
    lint.written_named? (Fren.FinSet.ofList ps) x = true ↔ x ∈ ps.flatMap (fun p => [p.first, p.second]) := by
  simp only [lint.written_named?, decide_eq_true_eq, Fren.FinSet.mem_ofList, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨p, h, e | e⟩ <;> exact ⟨p, h, by simp [e]⟩
  · rintro ⟨p, h, e | e⟩ <;> exact ⟨p, h, by simp [e]⟩

theorem wnegated_iff (ps : List lint.WrittenNegation) (x y : String) :
    lint.written_negated? (Fren.FinSet.ofList ps) x y = true ↔ (ps.any fun p => p.first == x && p.second == y) = true := by
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, lint.written_negated?, decide_eq_true_eq, Fren.FinSet.mem_ofList]
  constructor
  · rintro (h | h) <;> exact ⟨_, h, rfl, rfl⟩
  · rintro ⟨⟨a, b, o⟩, h, rfl, rfl⟩; cases o <;> simp_all

theorem written_fires (ps : List lint.WrittenNegation) (ds : List String) :
    lint.manual_at_most_one_any.ensure.rule (Fren.FinSet.ofList ps) (Fren.FinSet.ofList ds)
      (Fren.Core.manualAtMostOne lint.WrittenNegation.first lint.WrittenNegation.second lint.WrittenNegation.«obligation?» ps ds).1
      (Fren.Core.manualAtMostOne lint.WrittenNegation.first lint.WrittenNegation.second lint.WrittenNegation.«obligation?» ps ds).2 := by
  unfold lint.manual_at_most_one_any.ensure.rule
  simp only [wnamed_iff, wnegated_iff]
  simp only [Fren.Core.manualAtMostOne, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, List.all_eq_true,
    bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq, List.any_eq_false, Fren.FinSet.mem_ofList]
  refine and_congr (and_congr (and_congr ?_ ?_) ?_) ?_
  · constructor
    · rintro ⟨x, hx, y, hy, z, hz, h⟩
      exact ⟨x, y, z, ⟨⟨⟨⟨h.1.1, h.1.2⟩, h.2⟩, hx⟩, hy⟩, hz⟩
    · rintro ⟨x, y, z, ⟨⟨⟨⟨h1, h2⟩, h3⟩, hx⟩, hy⟩, hz⟩
      exact ⟨x, hx, y, hy, z, hz, by simp [h1, h2, h3]⟩
  · exact Iff.rfl
  · constructor
    · rintro h x y ⟨⟨hne, hx⟩, hy⟩
      rcases h x hx y hy with (e | g) | g
      · exact absurd e hne
      · exact Or.inl g
      · exact Or.inr g
    · intro h x hx y hy
      by_cases e : x = y
      · exact Or.inl (Or.inl e)
      · rcases h x y ⟨⟨e, hx⟩, hy⟩ with g | g
        · exact Or.inl (Or.inr g)
        · exact Or.inr g
  · constructor
    · rintro h ⟨p, hp, e⟩; exact absurd e (by simpa using h p hp)
    · intro h p hp; cases e : p.«obligation?»
      · simp
      · exact absurd ⟨p, hp, e⟩ h

theorem written_exactly (ps : List lint.WrittenNegation) (ds : List String) :
    lint.manual_at_most_one_any.ensure.fix (Fren.FinSet.ofList ps) (Fren.FinSet.ofList ds)
      (Fren.Core.manualAtMostOne lint.WrittenNegation.first lint.WrittenNegation.second lint.WrittenNegation.«obligation?» ps ds).1
      (Fren.Core.manualAtMostOne lint.WrittenNegation.first lint.WrittenNegation.second lint.WrittenNegation.«obligation?» ps ds).2 := by
  unfold lint.manual_at_most_one_any.ensure.fix
  simp only [wnamed_iff]
  simp only [Fren.Core.manualAtMostOne, Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.contains_iff_mem,
    Fren.FinSet.mem_ofList, ne_eq, Fren.FinSet.ofList_eq_empty, and_true]
  constructor
  · rintro ⟨⟨⟨x, hx⟩, h1⟩, h2⟩
    exact ⟨List.ne_nil_of_mem hx, fun y => ⟨h1 y, h2 y⟩⟩
  · rintro ⟨hne, h⟩
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil ds hne
    exact ⟨⟨⟨x, hx⟩, fun y hy => (h y).mp hy⟩, fun y hy => (h y).mpr hy⟩

impl manual_at_most_one_any: lint::manual_at_most_one_any for (ps : List lint.WrittenNegation) (ds : List String) {
  pairs := Fren.FinSet.ofList ps,
  disjunction := Fren.FinSet.ofList ds,
  fires? := (Fren.Core.manualAtMostOne lint.WrittenNegation.first lint.WrittenNegation.second lint.WrittenNegation.«obligation?» ps ds).1,
  exactly? := (Fren.Core.manualAtMostOne lint.WrittenNegation.first lint.WrittenNegation.second lint.WrittenNegation.«obligation?» ps ds).2,
} by
  intro ps ds _
  unfold lint.manual_at_most_one_any.ensures
  exact ⟨written_fires ps ds, written_exactly ps ds⟩

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

/-! ## Integers and natural numbers -/

instance : Fren.Finite Fren.Core.MinMax := ⟨[.min, .max], by intro x; cases x <;> simp⟩

def toMinMax : Fren.Core.MinMax → lint.MinMax
  | .min => .Min
  | .max => .Max

def toOrdered : Fren.Core.Ordered → lint.Ordered
  | .number => .Number
  | .enumeration => .Enumeration
  | .other => .OtherType

instance : Fren.Finite Fren.Core.Ordered := ⟨[.number, .enumeration, .other], by intro x; cases x <;> simp⟩

def toNatRole : Fren.Core.NatRole → lint.NatRole
  | .input => .Input
  | .output => .Output
  | .definedOutput => .DefinedOutput

def toBoundOp : Fren.Core.BoundOp → lint.BoundOp
  | .atLeast => .AtLeast
  | .atMost => .AtMost
  | .otherOp => .OtherOp

def toNatVariable (v : Fren.Core.NatVariable) : lint.NatVariable := ⟨v.name, toNatRole v.role, v.int⟩

def toNatConjunct (c : Fren.Core.NatConjunct) : lint.NatConjunct := ⟨c.assumption, toBoundOp c.op, c.left, c.right⟩

def toGiven : Fren.Core.Given → lint.Given
  | .givenInt => .Integer
  | .givenNat => .Natural

instance : Fren.Finite Fren.Core.Given := ⟨[.givenInt, .givenNat], by intro x; cases x <;> simp⟩

theorem natBounds_iff (v : Fren.Core.NatVariable) (c : Fren.Core.NatConjunct) :
    Fren.Core.natBounds v c = true ↔ lint.bounds? (toNatVariable v) (toNatConjunct c) := by
  rcases v with ⟨n, r, i⟩; rcases c with ⟨a, o, l, rt⟩
  cases r <;> cases o <;> cases i <;> cases a <;>
    simp [Fren.Core.natBounds, lint.bounds?, toNatVariable, toNatConjunct, toNatRole, toBoundOp, fren_spec]

-- Both front ends find each variable's bound with `manualNatBounds`, which
-- asks `manualNatAt` of the conjuncts of the component's assumptions and
-- guarantees, in order, and drop at the end of the file the reports of the
-- variables that an instance, a refinement or an `impl` gives an `Int`.
impl manual_nat: lint::manual_nat for (v : Fren.Core.NatVariable) (cs : List Fren.Core.NatConjunct)
    (us : List Fren.Core.Given) (k : Int) {
  var := toNatVariable v,
  conjuncts := Fren.Seq.ofList (cs.map toNatConjunct),
  uses := Fren.Seq.ofList (us.map toGiven),
  k := k,
  position := ((Fren.Core.manualNatAt v cs (us.contains .givenInt)).map Int.ofNat).getD (-1),
} by
  intro v cs us k _
  have hg : (lint.Given.Integer ∈ Fren.Seq.ofList (us.map toGiven)) ↔ us.contains .givenInt = true := by
    simp only [Fren.Seq.mem_iff, Fren.Seq.toList_ofList, List.mem_map, List.contains_iff_mem]
    constructor
    · rintro ⟨x, hx, h⟩
      cases x <;> simp_all [toGiven]
    · intro h
      exact ⟨_, h, rfl⟩
  have hnth : ∀ i : Nat, (h : i < cs.length) →
      (Fren.Seq.ofList (cs.map toNatConjunct)).nth (i : Int) = toNatConjunct cs[i] := by
    intro i h
    rw [Fren.Seq.nth_of_lt _ _ (by omega) (by simpa using h)]
    simp
  have hb : ∀ c, Fren.Core.natBounds v c = true ↔ lint.bounds? (toNatVariable v) (toNatConjunct c) := natBounds_iff v
  simp only [fren_spec] at hb
  simp only [fren_spec, hg, Fren.Core.manualNatAt]
  by_cases hk : us.contains .givenInt = true
  · simp only [hk, if_true, Option.map_none, Option.getD_none]
    simp
  · simp only [hk, Bool.false_eq_true, if_false, false_implies, true_and]
    cases hf : cs.findIdx? (Fren.Core.natBounds v) with
    | none =>
      rw [List.findIdx?_eq_none_iff] at hf
      simp only [Option.map_none, Option.getD_none, ne_eq, not_true_eq_false, false_implies, true_and,
        not_false_eq_true, true_implies]
      intro h0
      obtain ⟨⟨hk0, hkl⟩, hbk⟩ := h0
      exfalso
      have hk' : k.toNat < cs.length := by simp at hkl; omega
      have e : k = ((k.toNat : Nat) : Int) := by omega
      rw [e, hnth _ hk'] at hbk
      have h := (hb cs[k.toNat]).mpr
      rw [hf _ (List.getElem_mem hk')] at h
      exact absurd (h (by simpa using hbk)) (by simp)
    | some i =>
      rw [List.findIdx?_eq_some_iff_getElem] at hf
      obtain ⟨hi, hp, hmin⟩ := hf
      simp only [Option.map_some, Option.getD_some, Int.ofNat_eq_natCast, hnth _ hi]
      refine ⟨fun _ => ⟨⟨by omega, by simpa using hi⟩, by simpa using (hb cs[i]).mp hp⟩, fun _ h0 => ?_⟩
      obtain ⟨⟨hk0, hkl⟩, hbk⟩ := h0
      have hk' : k.toNat < cs.length := by simp at hkl; omega
      have e : k = ((k.toNat : Nat) : Int) := by omega
      rw [e] at hbk
      simp only [hnth _ hk'] at hbk
      refine ⟨by omega, ?_⟩
      rcases Nat.lt_or_ge k.toNat i with hlt | hge
      · exact absurd ((hb _).mpr (by simpa using hbk)) (hmin k.toNat hlt)
      · omega

-- Both front ends ask `refinementGiven` at each variable that a refinement
-- reads by name.
impl refinement_given: lint::refinement_given for (i : Bool) (a c : Fren.Core.Given) {
  input? := i,
  abstract_type := toGiven a,
  concrete_type := toGiven c,
  side := if (Fren.Core.refinementGiven i a c).1 then .Concrete else .Abstract,
  given := toGiven (Fren.Core.refinementGiven i a c).2,
}

-- The rest are decided in `opReports`, in both front ends, from the type
-- that each front end records for each ordering.
impl manual_abs: lint::manual_abs for (o : Fren.Core.Ordered) (c : Comparison) (t : Bool) {
  compared := toOrdered o,
  op := toComparison c,
  negated_then? := t,
  fires? := Fren.Core.manualAbs o c t,
}

impl manual_abs_diff: lint::manual_abs_diff for (c : Comparison) (o : Fren.Core.Ordered) (a b : String)
    (t e : String × String) {
  op := toComparison c,
  compared := toOrdered o,
  a := a,
  b := b,
  then_branch := ⟨t.1, t.2⟩,
  else_branch := ⟨e.1, e.2⟩,
  fires? := Fren.Core.manualAbsDiffRule c o a b t e,
} by
  intro c o a b t e _
  rcases t with ⟨t1, t2⟩; rcases e with ⟨e1, e2⟩
  cases c <;> cases o <;> simp [fren_spec, toOrdered, toComparison, Fren.Core.manualAbsDiffRule, Fren.Core.manualAbsDiff,
    Comparison.below, Comparison.above]

impl manual_min_max: lint::manual_min_max for (c : Comparison) (o : Fren.Core.Ordered) (a b t e : String)
    (al bl : Bool) {
  op := toComparison c,
  compared := toOrdered o,
  a := ⟨a, al⟩,
  b := ⟨b, bl⟩,
  then_branch := t,
  else_branch := e,
  fires? := (Fren.Core.manualMinMaxRule c o a b t e al bl).isSome,
  method := toMinMax (((Fren.Core.manualMinMaxRule c o a b t e al bl).map (·.1)).getD .min),
  receiver_left? := ((Fren.Core.manualMinMaxRule c o a b t e al bl).map (·.2)).getD true,
} by
  intro c o a b t e al bl _
  cases c <;> cases o <;> cases al <;> cases bl <;> simp [fren_spec, toOrdered, toComparison, toMinMax,
    Fren.Core.manualMinMaxRule, Fren.Core.manualMinMax, Comparison.below, Comparison.above] <;>
    (try refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩) <;> simp_all <;> split <;> simp_all

impl manual_clamp: lint::manual_clamp for (o : Fren.Core.Ordered) (f s : Comparison) (a b : Int) {
  compared := toOrdered o,
  first_op := toComparison f,
  second_op := toComparison s,
  first := a,
  second := b,
  fires? := Fren.Core.manualClamp o f s a b,
  low_first? := f.below,
} by
  intro o f s a b _
  cases o <;> cases f <;> cases s <;> simp [fren_spec, toOrdered, toComparison, Fren.Core.manualClamp, Comparison.below, Comparison.above]

def toSummand (p : Fren.Core.Summand) : lint.Summand := ⟨p.text, p.divisor?.isSome, p.divisor?.getD ""⟩

impl manual_rem_euclid: lint::manual_rem_euclid for (p q : Fren.Core.Summand) (k : String) {
  p := toSummand p,
  q := toSummand q,
  k := k,
  fires? := Fren.Core.manualRemEuclidRule p q k,
} by
  intro p q k _
  rcases p with ⟨pt, _ | pd⟩ <;> rcases q with ⟨qt, _ | qd⟩ <;> simp [fren_spec, toSummand, Fren.Core.manualRemEuclidRule]
  done

impl modulo_one: lint::modulo_one for (k : Int) {
  divisor := k,
  fires? := Fren.Core.moduloOne k,
} by
  intro k _
  simp [fren_spec, Fren.Core.moduloOne]

impl min_max: lint::min_max for (i o : Fren.Core.MinMax) (a b : Int) {
  inner := toMinMax i,
  outer := toMinMax o,
  a := a,
  b := b,
  fires? := Fren.Core.minMax i o a b,
} by
  intro i o a b _
  cases i <;> cases o <;> simp [fren_spec, toMinMax, Fren.Core.minMax]

-- `erasingOpAt?` asks `erasingDivision` at each `div` and `mod`, with the
-- value of a dividend that is an integer literal.
impl erasing_division: lint::erasing_division for (d : Option Int) {
  literal? := d.isSome,
  dividend := d.getD 0,
  fires? := Fren.Core.erasingDivision d,
} by
  intro d _
  cases d <;> simp [fren_spec, Fren.Core.erasingDivision]

impl eq_op_method: lint::eq_op_method for (r a : String) {
  receiver := r,
  argument := a,
  fires? := Fren.Core.eqOpMethod r a,
} by
  intro r a _
  simp [fren_spec, Fren.Core.eqOpMethod]

trusted lint::manual_nat_input_written: "a model of a component, checked by the refinements in its section"
trusted lint::manual_nat_input_fixed: "a model of a component, checked by the refinements in its section"
trusted lint::manual_nat_output_written: "a model of a component, checked by the refinement in its section"
trusted lint::manual_nat_output_fixed: "a model of a component, checked by the refinement in its section"
trusted lint::manual_abs_written: "a model of an expression, checked by the refinements in its section"
trusted lint::manual_abs_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::manual_min_max_written: "a model of an expression, checked by the refinements in its section"
trusted lint::manual_min_max_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::manual_rem_euclid_written: "a model of an expression, checked by the refinements in its section"
trusted lint::manual_rem_euclid_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::eq_op_method_written: "a model of an expression, checked by the refinements in its section"
trusted lint::eq_op_method_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::integer_values_written: "a model of an expression, checked by the refinements in its section"
trusted lint::integer_values_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::erasing_division_written: "a model of an expression, checked by the refinements in its section"
trusted lint::erasing_division_fixed: "a model of an expression, checked by the refinements in its section"

/-! ## Patterns, matches and tables -/

impl range_union: lint::range_union for (lo1 hi1 lo2 hi2 n : Int) {
  lo1 := lo1,
  hi1 := hi1,
  lo2 := lo2,
  hi2 := hi2,
  n := n,
  joined? := Fren.Core.lowerAtMost (some lo2) (some (hi1 + 1)),
} by
  intro lo1 hi1 lo2 hi2 n _
  simp [fren_spec, Fren.Core.lowerAtMost]

-- These components compute, over a model of patterns, arms and rows, what
-- each front end reads from the syntax with `Fren.Core.PatNode` and the
-- functions of `Fren.Core` that decide the lints; the ui tests run both
-- front ends over the same cases, and the snapshots and fix tests the
-- `fren` command. The components' expectations check each fix over the
-- model.
tested lint::collapsible_match: "test/ui/lints/patterns_tables.fren", "test/cli/lints/style/f0832_collapsible_match.fren",
  "test/cli/fix/patterns_tables.fren"
tested lint::match_overlapping_arm: "test/ui/lints/patterns_tables.fren", "test/cli/lints/style/f0835_match_overlapping_arm.fren"
tested lint::wildcard_in_or_patterns: "test/ui/lints/patterns_tables.fren", "test/cli/lints/complexity/f0834_wildcard_in_or_patterns.fren",
  "test/cli/fix/patterns_tables.fren"
tested lint::manual_range_patterns: "test/ui/lints/patterns_tables.fren", "test/cli/lints/complexity/f0833_manual_range_patterns.fren",
  "test/cli/fix/patterns_tables.fren"
tested lint::unnested_or_patterns: "test/ui/lints/patterns_tables.fren", "test/cli/lints/pedantic/f0836_unnested_or_patterns.fren",
  "test/cli/fix/patterns_tables.fren"
tested lint::match_bool: "test/ui/lints/patterns_tables.fren", "test/cli/lints/pedantic/f0837_match_bool.fren",
  "test/cli/fix/patterns_tables.fren"
tested lint::single_match_else: "test/ui/lints/pedantic.fren", "test/cli/lints/pedantic/f0771_single_match_else.fren",
  "test/cli/fix/patterns_tables.fren"
tested lint::manual_table: "test/ui/lints/patterns_tables.fren", "test/cli/lints/pedantic/f0838_manual_table.fren"
tested lint::same_rows: "test/ui/lints/patterns_tables.fren", "test/cli/fix/patterns_tables.fren"

trusted lint::wildcard_in_or_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::wildcard_in_or_fixed: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::manual_range_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::manual_range_fixed: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::unnested_or_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::unnested_or_fixed: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::collapsible_match_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::collapsible_match_fixed: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::collapsible_shadow_written: "a model of an expression, checked against its nested form by the refinements in its section"
trusted lint::collapsible_shadow_fixed: "a model of an expression, checked against its nested form by the refinements in its section"
trusted lint::match_bool_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::match_bool_fixed: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::manual_table_written: "a model of an expression, checked against the table its message suggests by the refinements in its section"
trusted lint::manual_table_fixed: "a model of an expression, checked against the table its message suggests by the refinements in its section"
trusted lint::same_rows_written: "a model of an expression, checked against its fix by the refinements in its section"
trusted lint::same_rows_fixed: "a model of an expression, checked against its fix by the refinements in its section"


/-! ## Local definitions and quantifiers -/

instance : Fren.Finite Fren.Core.RunPlace :=
  ⟨[.free, .body, .condition, .operand, .receiver], by intro x; cases x <;> simp⟩

def toRunPlace : Fren.Core.RunPlace → lint.RunPlace
  | .free => .Free
  | .body => .Body
  | .condition => .Condition
  | .operand => .Operand
  | .receiver => .Receiver

-- `manualForallAt` places its quantifier with `quantifierParenthesized`, at
-- `RunPlace.ofSlot` of the run's slot.
impl quantifier_parentheses: lint::quantifier_parentheses for (p : Fren.Core.RunPlace) (f w e : Bool) {
  place := toRunPlace p,
  followed? := f,
  whole? := w,
  enclosed? := e,
  parenthesized? := Fren.Core.quantifierParenthesized p f w e,
} by
  intro p f w e _
  cases p <;> cases f <;> cases w <;> cases e <;> simp [fren_spec, toRunPlace, Fren.Core.quantifierParenthesized]

-- Both front ends read these from their syntax trees, with `mentions`
-- (`pathMentions`), `declaredNames` and `clauseMentions`, and decide them
-- with `letAndReturn`, `redundantLocal`, `manualForallAt` and
-- `trivialQuantifier`; a tree of nodes and relations has too many values
-- for `decide`, so the ui and fix tests check them against the components.
-- keep-sorted start
tested lint::let_and_return: "test/ui/lints/let_quantifiers.fren"
tested lint::manual_forall: "test/ui/lints/let_quantifiers.fren"
tested lint::redundant_locals: "test/ui/lints/let_quantifiers.fren"
tested lint::scope: "test/ui/lints/let_quantifiers.fren"
tested lint::trivial_quantifier: "test/ui/lints/let_quantifiers.fren"
tested lint::unused_bound: "test/ui/lints/let_quantifiers.fren"
tested lint::unused_definitions: "test/ui/lints/let_quantifiers.fren"
-- keep-sorted end

-- The models of the expressions that the refinements of these lints compare.
-- keep-sorted start
trusted lint::let_and_return_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::let_and_return_written: "a model of an expression, checked by the refinements in its section"
trusted lint::manual_forall_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::manual_forall_written: "a model of an expression, checked by the refinements in its section"
trusted lint::redundant_locals_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::redundant_locals_written: "a model of an expression, checked by the refinements in its section"
trusted lint::trivial_quantifier_fixed: "a model of an expression, checked by the refinements in its section"
trusted lint::trivial_quantifier_written: "a model of an expression, checked by the refinements in its section"
-- keep-sorted end

end Fren.Impls
