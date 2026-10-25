-- keep-sorted start
import Impls.Lang
import Impls.View
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
    .variant, .record, .abstractType, .constant],
    by intro x; cases x <;> simp⟩

instance : Fren.Finite Comparison := ⟨Comparison.all.toList, by intro x; cases x <;> simp [Comparison.all]⟩

instance : Fren.Finite Head := ⟨[.not, .unequal, .ite, .when, .unless, .other], by intro x; cases x <;> simp⟩

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
  | .decidability => .Decidability

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
impl length_zero: lint::length_zero for (c : Comparison) (b : Int) (l : Bool) {
  op := toComparison c,
  bound := b,
  left? := l,
  fires? := (Fren.Core.lengthZero c b l).1,
  empty? := (Fren.Core.lengthZero c b l).2,
} by
  intro c b l _
  cases c <;> cases l <;> simp [fren_spec, toComparison, Fren.Core.lengthZero, Fren.Core.Comparison.mirror]

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

impl match_like_membership: lint::match_like_membership for (bb np w wt : Bool) (t f : Nat) {
  bool_bodies? := bb,
  no_payloads? := np,
  wildcard? := w,
  wildcard_true? := wt,
  n_true := t,
  n_false := f,
  fires? := (Fren.Core.matchMembership bb np w wt t f).1,
  negated? := (Fren.Core.matchMembership bb np w wt t f).2,
} by
  intro bb np w wt t f _
  cases bb <;> cases np <;> cases w <;> cases wt <;> simp [fren_spec, Fren.Core.matchMembership] <;> omega

impl wildcard_single_variant: lint::wildcard_single_variant for (n : Nat) {
  n_matched := n,
  fires? := Fren.Core.wildcardSingle n,
} by
  intro n _
  simp [fren_spec, Fren.Core.wildcardSingle]
  omega

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

impl case_split_reqs: lint::case_split_reqs for (n r : Nat) {
  n_cases := n,
  n_repeated := r,
  fires? := Fren.Core.caseSplitReqs n r,
} by
  intro n r _
  simp [fren_spec, Fren.Core.caseSplitReqs] <;> omega

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

impl double_parens: lint::double_parens for (d : Nat) {
  depth := d,
  fires? := Fren.Core.doubleParens d,
} by
  intro d _
  simp [fren_spec, Fren.Core.doubleParens]
  omega

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
} by
  intro i o _
  cases i <;> cases o <;> simp [fren_spec, toMethod, toChainFix, Fren.Core.methodChain]

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

-- `trivialPattern?` reads the pattern's characters; the spec states the
-- same with a pattern, which the tests check against it.
tested lint::trivial_pattern: "test/ui/lints/methods.fren", "test/cli/lints/style/f0744_trivial_pattern.fren"

end Fren.Impls
