-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

-- For every `match`: the counts of the arms and alternatives that are not
-- useful, and whether it is exhaustive, which `checkMatch` decides by.
impl match_arms: lang::match_arms for (a b : Nat) (e : Bool) {
  n_useless_arms := a,
  n_useless_alternatives := b,
  exhaustive? := e,
  accepted? := Fren.Core.matchArmsAccepted (a + b) e,
} by
  intro a b e _
  cases e <;> simp [fren_spec, Fren.Core.matchArmsAccepted] <;> omega

-- For every pattern test: whether it may bind names, and the counts that
-- `checkPatternTest` decides by.
impl pattern_test: lang::pattern_test for (k : Bool) (b u : Nat) (m : Bool) {
  binds? := k,
  n_bound := b,
  n_useless_alternatives := u,
  matches_some? := m,
  accepted? := Fren.Core.patternTestAccepted k b u m,
} by
  intro k b u m _
  cases k <;> cases m <;> simp [fren_spec, Fren.Core.patternTestAccepted]

def toTestContext : Fren.Core.TestContext → lang.TestContext
  | .whenCondition => .WhenCondition
  | .unlessCondition => .UnlessCondition
  | .ifCondition => .IfCondition
  | .orOperand => .OrOperand
  | .notOperand => .NotOperand
  | .standalone => .Standalone

def toSite : Fren.Core.TestSite → lang.Site
  | .operand k => .Operand k
  | .body => .Body
  | .elseBranch => .ElseBranch
  | .outside => .Outside

-- For every pattern test and mention: both front ends decide whether the
-- test binds with `testBinds`, and which part of a `when`, an `if` or a
-- chain of `and` sees its names with `binderVisible`. That each classifies
-- its syntax into the right context and positions is not proved here, but
-- tested by both on the same ui tests (`test/ui/lang/pattern_binders*.fren`).
impl test_scope: lang::test_scope for (c : Fren.Core.TestContext) (n t : Nat) (s : Fren.Core.TestSite) {
  context := toTestContext c,
  operands := n,
  test_at := t,
  site := toSite s,
  visible? := Fren.Core.binderVisible c t n s,
  binds? := Fren.Core.testBinds c t n,
} by
  intro c n t s _
  cases c <;> cases s <;>
    simp [fren_spec, toTestContext, toSite, Fren.Core.binderVisible, Fren.Core.testBinds,
      Fren.Core.TestContext.bodySees] <;> omega

/-! ## Patterns (`Reqs/Lang/Patterns`) -/

-- For every range and integer: the bounds as `Option`s, as both front ends
-- and the evaluator read them.
impl range_pattern: lang::range_pattern for (hl : Bool) (l : Int) (hu : Bool) (u : Int) (inc : Bool) (v : Int) {
  has_lower? := hl,
  lower := l,
  has_upper? := hu,
  upper := u,
  inclusive? := inc,
  value := v,
  matches? := Fren.Core.rangeMatches (if hl then some l else none) (if hu then some u else none) inc v,
  empty? := Fren.Core.rangeEmpty (if hl then some l else none) (if hu then some u else none) inc,
} by
  intro hl l hu u inc v _
  cases hl <;> cases hu <;> cases inc <;> simp [fren_spec, Fren.Core.rangeMatches, Fren.Core.rangeEmpty]

def toHeadKind : Fren.Core.HeadKind → lang.HeadKind
  | .constructor => .Constructor
  | .wildcard => .Wildcard
  | .or => .Or

-- For every step of `useful`, which calls `usefulStep` with the smaller
-- problems as functions.
impl usefulness: lang::usefulness for (c r : Nat) (h : Fren.Core.HeadKind) (k sp ss d sa : Bool) {
  columns := c,
  rows := r,
  head := toHeadKind h,
  complete? := k,
  specialized? := sp,
  some_specialized? := ss,
  default? := d,
  some_alternative? := sa,
  useful? := Fren.Core.usefulStep c r h k (fun _ => sp) (fun _ => ss) (fun _ => d) (fun _ => sa),
} by
  intro c r h k sp ss d sa _
  cases h <;> cases k <;> by_cases hc : c = 0 <;>
    simp [fren_spec, toHeadKind, Fren.Core.usefulStep, hc] <;> omega

-- For every row's head and constructor, by the head's kind.
impl specialize: lang::specialize for (p : Fren.Core.Pat) (c : Fren.Core.Ctor) (a : Nat) {
  head := toHeadKind p.headKind,
  same? := p.sameCtor c,
  arity := a,
  n_args := p.args.length,
  kept? := (Fren.Core.specializeHead c a p).isSome,
  added := ((Fren.Core.specializeHead c a p).map (·.length)).getD 0,
} by
  intro p c a _
  simp only [Fren.Core.specializeHead]
  cases p.headKind <;> cases p.sameCtor c <;> simp [fren_spec, toHeadKind]

/-- `some ()` where `b` holds: a step of overlap read as a decision. -/
def someIf (b : Bool) : Option Unit := if b then some () else none

-- For every step of `Pat.overlapWit?`, which calls `overlapStep` with the
-- smaller problems as functions; its decision is whether it has a witness.
impl overlap: lang::overlap for (f g : Fren.Core.HeadKind) (same args fm gm alt : Bool) {
  first := toHeadKind f,
  second := toHeadKind g,
  same? := same,
  args_overlap? := args,
  first_matches? := fm,
  second_matches? := gm,
  some_alternative? := alt,
  overlap? := (Fren.Core.overlapStep f g same (fun _ => someIf args) (fun _ => someIf fm) (fun _ => someIf gm)
    (fun _ => someIf alt)).isSome,
} by
  intro f g same args fm gm alt _
  cases f <;> cases g <;> cases same <;> cases args <;> cases fm <;> cases gm <;> cases alt <;>
    simp [fren_spec, toHeadKind, Fren.Core.overlapStep, someIf]

def toColumnType : Fren.Core.ColumnKind → lang.ColumnType
  | .enumeration => .EnumType
  | .boolean => .BoolType
  | .integer => .IntType
  | .string => .StringType
  | .other => .OtherType

-- For every column, as `columnCtors` decides it.
impl signature_complete: lang::signature_complete for (k : Fren.Core.ColumnKind) (n m : Nat) (t f i : Bool) {
  column := toColumnType k,
  n_variants := n,
  n_named := m,
  has_true? := t,
  has_false? := f,
  covers_integers? := i,
  complete? := Fren.Core.signatureComplete k n m t f i,
} by
  intro k n m t f i _
  cases k <;> simp [fren_spec, toColumnType, Fren.Core.signatureComplete] <;> omega

-- For every payload and mention: the elaborators' check, which both front
-- ends call through `variantMentionMsg?`.
impl variant_mention: lang::variant_mention for (n : Nat) (a : Bool) {
  payload := n,
  applied? := a,
  accepted? := Fren.Core.variantMentionAccepted n a,
} by
  intro n a _
  cases a <;> rcases n with _ | n <;> simp [fren_spec, Fren.Core.variantMentionAccepted] <;> omega

end Fren.Impls
