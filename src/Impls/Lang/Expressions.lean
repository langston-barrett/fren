-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-- A mention, as the spec writes it. -/
def toMention : Fren.Core.Mention → lang.Mention
  | .var x => .Var x
  | .fn f => .Fn f

/-- The kind (`lang::ExprKind`) of an expression of kind `k`. -/
def toExprKind : Fren.Core.MentionKind → lang.ExprKind
  | .literal => .Literal
  | .constant => .Constant
  | .variable n => .Variable n
  | .definition => .Definition
  | .binder => .Binder
  | .bound => .BoundName
  | .construction => .Construction
  | .method => .Method
  | .uninterpreted f => .Uninterpreted f
  | .defined => .Defined
  | .compound => .Compound

/-- What `ms` mention, as a set of the spec's mentions. -/
def mentionSet (ms : List Fren.Core.Mention) : Fren.FinSet lang.Mention := Fren.FinSet.ofList (ms.map toMention)

-- For every expression's shape: what each kind mentions, and the walk over
-- a shape that both front ends decide by. That each front end classifies
-- its syntax into the right kinds is not proved here, but tested by both on
-- the same ui tests, whose messages name what each operand of a nonlinear
-- product mentions.
impl mentions: lang::mentions for (k : Fren.Core.MentionKind) (ps : List Fren.Core.MentionShape) {
  form := toExprKind k,
  sub_mentioned := mentionSet (Fren.Core.MentionShape.allMentioned ps),
  mentioned := mentionSet (Fren.Core.MentionShape.node k ps).mentioned,
  mentions? := (Fren.Core.MentionShape.node k ps).mentions,
} by
  intro k ps h
  cases k <;> simp_all [fren_spec, toExprKind, mentionSet, toMention, Fren.Core.MentionShape.mentions,
    Fren.Core.MentionShape.mentioned, Fren.Core.kindMentioned, Fren.FinSet.ext_iff, or_comm]
  all_goals cases Fren.Core.MentionShape.allMentioned ps <;> simp [Fren.FinSet.ext_iff]
  all_goals exact ⟨_, fun h => absurd rfl h⟩

def toGuardedOperand : Fren.Core.GuardedOperand → lang.GuardedOperand
  | .whenBody => .WhenBody
  | .unlessBody => .UnlessBody
  | .thenBranch => .ThenBranch
  | .elseBranch => .ElseBranch
  | .andRight => .AndRight
  | .orRight => .OrRight
  | .armGuard => .ArmGuard
  | .armBody => .ArmBody

-- For every operand and condition: the guard that both front ends add, by
-- `GuardedOperand.guard`, here over the condition's value, a `Bool`. That
-- each front end calls it with the right operand is not proved here, but
-- tested by both on the same ui tests.
impl guard: lang::guard for (o : Fren.Core.GuardedOperand) (h : Bool) {
  operand := toGuardedOperand o,
  condition := lang.truth h,
  holds? := h,
  evaluated? := o.guard h (!h),
} by
  intro o h _
  cases o <;> cases h <;>
    simp [fren_spec, toGuardedOperand, lang.truth, Fren.Core.GuardedOperand.guard, Fren.Core.GuardedOperand.whenHolds]

-- For every two operands, by what each mentions.
impl linear_product: lang::linear_product for (a b : List Fren.Core.Mention) {
  a_mentioned := mentionSet a,
  b_mentioned := mentionSet b,
  accepted? := Fren.Core.productAccepted a b,
} by
  intro a b _
  cases a <;> cases b <;> simp [fren_spec, Fren.Core.productAccepted, mentionSet]

def toDivisorForm : Fren.Core.DivisorForm → lang.DivisorForm
  | .literal => .LiteralDivisor
  | .knownConstant => .KnownConstant
  | .unknownConstant => .UnknownConstant
  | .other => .OtherDivisor

-- For every divisor, by the form and value that both front ends give
-- `Fren.Core.checkDivisor`.
impl divisor: lang::divisor for (f : Fren.Core.DivisorForm) (v : Int) {
  form := toDivisorForm f,
  value := v,
  accepted? := Fren.Core.divisorAccepted f v,
} by
  intro f v _
  cases f <;> simp [fren_spec, toDivisorForm, Fren.Core.divisorAccepted]

def toCardinality : Fren.Core.Cardinality → lang.Cardinality
  | .exactlyOne => .Exactly
  | .atMostOne => .AtMost

-- For every operator and number of arguments that are `true`: the value that
-- the evaluator gives it. That both front ends' translations, a sum compared
-- with 1, agree with it is not proved here, but confirmed on the solver's
-- models and tested by both on the same ui tests.
impl cardinality: lang::cardinality for (c : Fren.Core.Cardinality) (n k : Nat) {
  op := toCardinality c,
  n_args := n,
  n_true := k,
  value? := c.holds k,
} by
  intro c n k _
  cases c <;> simp [fren_spec, toCardinality, Fren.Core.Cardinality.holds] <;> omega

-- For every chained comparison, by the counts of its operators' kinds that
-- `Fren.Core.checkChain`, which both front ends call, takes.
impl comparison_chain: lang::comparison_chain for (a d o : Nat) {
  n_ascending := a,
  n_descending := d,
  n_other := o,
  accepted? := Fren.Core.chainAccepted a d o,
} by
  intro a d o _
  simp [fren_spec, Fren.Core.chainAccepted] <;> omega

end Fren.Impls
