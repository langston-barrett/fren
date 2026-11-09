import Fren.Impl
import Fren.Literate
import FrenBase.Binding
import FrenExpr

open Fren.Lang

#fren_md "Types.md"

set_option warningAsError true in
#fren_check

namespace Spec.Language.Types

/-- A local has its actual context entry, not merely some type at an
in-bounds index. This law uses the existing production binding primitive. -/
theorem local_type_unique {Ty : Type} (ctx : FrenBase.Binding.Context Ty)
    (i : Nat) (a b : Ty) (ha : FrenBase.Binding.HasType ctx i a)
    (hb : FrenBase.Binding.HasType ctx i b) : a = b := by
  exact Option.some.inj (ha.symm.trans hb)

theorem local_type_scoped {Ty : Type} (ctx : FrenBase.Binding.Context Ty)
    (i : Nat) (ty : Ty) (h : FrenBase.Binding.HasType ctx i ty) :
    FrenBase.Binding.InScope ctx.length i :=
  FrenBase.Binding.hasType_scoped h

-- Equal lengths and valid indices alone cannot choose a local's type.
#guard FrenBase.Binding.HasType [true, false] 0 true
#guard ¬ FrenBase.Binding.HasType [true, false] 0 false
#guard FrenBase.Binding.HasType [false, true] 0 false
#guard ¬ FrenBase.Binding.HasType ([] : List Bool) 0 true

/-- The normative payload type uses the same generic production type carrier.
No tag/identity pair or display-string encoding is involved. -/
def coreType : spec.types.Ty → FrenExpr.ValueType (Fren.Seq String)
  | .Boolean => .bool
  | .Integer => .int
  | .Nominal owner => .enum owner

theorem core_type_injective : Function.Injective coreType := by
  intro a b h
  cases a <;> cases b <;> simp_all [coreType]

/-- Exact equality on canonical components instantiates production compatibility. -/
theorem core_compatibility (a b : spec.types.Ty) :
    @FrenExpr.ValueType.compatible (Fren.Seq String)
      ⟨fun x y => decide (x = y)⟩ (coreType a) (coreType b) = true ↔
        spec.types.compatible_type? a b := by
  cases a <;> cases b <;>
    simp [coreType, FrenExpr.ValueType.compatible, fren_spec]

/-- These adapters change only the spec's finite tags, not the deciding
implementation. Int equality atoms instantiate the same generic production
primitive that the walker instantiates with canonical ItemId. -/
def primitiveType : spec.types.ValueKind → Int → FrenExpr.ValueType Int
  | .Boolean, _ => .bool
  | .Integer, _ => .int
  | .Nominal, id => .enum id

def primitiveKind : FrenExpr.ValueType Int → spec.types.ValueKind
  | .bool => .Boolean | .int => .Integer | .enum _ => .Nominal

def primitiveUnary : spec.types.UnaryOp → FrenAst.UnaryOp
  | .Neg => .neg | .Not => .not

def primitiveBinary : spec.types.BinaryOp → FrenAst.BinaryOp
  | .Add => .add | .Sub => .sub | .Mul => .mul | .Div => .div | .Mod => .mod
  | .Lt => .lt | .Le => .le | .Gt => .gt | .Ge => .ge
  | .And => .and | .Or => .or | .Iff => .iff | .Eq => .eq | .Ne => .ne

/-- The normative unary rule agrees with the actual generic primitive. -/
theorem core_unary (op : spec.types.UnaryOp) (operand result : spec.types.Ty) :
    @FrenExpr.unary (Fren.Seq String) ⟨fun x y => decide (x = y)⟩
      (primitiveUnary op) (coreType operand) = some (coreType result) ↔
        spec.types.unary_type? op operand result := by
  cases op <;> cases operand <;> cases result <;>
    simp [coreType, primitiveUnary, FrenExpr.unary, FrenExpr.unaryOperand,
      FrenExpr.ValueType.compatible, fren_spec]

/-- Every operator and nominal identity is covered; there is no bounded enum domain. -/
theorem core_binary (op : spec.types.BinaryOp) (left right result : spec.types.Ty) :
    @FrenExpr.binary (Fren.Seq String) ⟨fun x y => decide (x = y)⟩
      (primitiveBinary op) (coreType left) (coreType right) = some (coreType result) ↔
        spec.types.binary_type? op left right result := by
  cases op <;> cases left <;> cases right <;> cases result <;>
    simp [coreType, primitiveBinary, FrenExpr.binary, FrenExpr.binaryOperand,
      FrenExpr.binaryResult, FrenExpr.ValueType.compatible, fren_spec, eq_comm]

impl compatibility: compatible for
    (left right : spec.types.ValueKind) (left_id right_id : Int) {
  left := left, right := right, left_id := left_id, right_id := right_id,
  same? := (primitiveType left left_id).compatible (primitiveType right right_id)
} by
  intro left right left_id right_id _
  cases left <;> cases right <;>
    simp [fren_spec, primitiveType, FrenExpr.ValueType.compatible, beq_iff_eq]

impl unary: unary for (op : spec.types.UnaryOp) (operand : spec.types.ValueKind) {
  op := op, operand := operand,
  accepted? := (FrenExpr.unary (primitiveUnary op) (primitiveType operand 0)).isSome,
  result := primitiveKind ((FrenExpr.unary (primitiveUnary op) (primitiveType operand 0)).getD .bool)
} by
  intro op operand _
  cases op <;> cases operand <;>
    simp [fren_spec, primitiveUnary, primitiveType, primitiveKind, FrenExpr.unary,
      FrenExpr.unaryOperand, FrenExpr.ValueType.compatible]

impl binary: binary for
    (op : spec.types.BinaryOp) (left right : spec.types.ValueKind) (left_id right_id : Int) {
  op := op, left := left, right := right, left_id := left_id, right_id := right_id,
  accepted? := (FrenExpr.binary (primitiveBinary op) (primitiveType left left_id)
    (primitiveType right right_id)).isSome,
  result := primitiveKind ((FrenExpr.binary (primitiveBinary op) (primitiveType left left_id)
    (primitiveType right right_id)).getD .bool)
} by
  intro op left right left_id right_id _
  cases op <;> cases left <;> cases right <;>
    simp [fren_spec, primitiveBinary, primitiveType, primitiveKind, FrenExpr.binary,
      FrenExpr.binaryOperand, FrenExpr.binaryResult, FrenExpr.ValueType.compatible, beq_iff_eq]
  all_goals by_cases h : left_id = right_id <;> simp_all [primitiveKind, eq_comm]

/-- Production contexts list the same entries nearest first. -/
def nearest {α : Type} : spec.types.Snoc α → List α
  | .Empty => []
  | .Extend earlier x => x :: nearest earlier

theorem nearest_length {α : Type} [Inhabited α] (xs : spec.types.Snoc α) :
    (nearest xs).length = spec.types.length _ xs := by
  induction xs with
  | Empty => rfl
  | Extend earlier x ih => simp [nearest, spec.types.length, ih]

/-- The level-to-index refinement: the Core entry at level `level` is the
production entry at nearest-first index `|xs| - 1 - level`. -/
theorem lookup_nearest {α : Type} [Inhabited α] (xs : spec.types.Snoc α) (level : Nat)
    (bound : level < spec.types.length _ xs) :
    spec.types.lookup _ xs level =
      FrenBase.Binding.lookup (nearest xs) (spec.types.length _ xs - 1 - level) := by
  induction xs with
  | Empty => simp [spec.types.length] at bound
  | Extend earlier x ih =>
    simp only [spec.types.length] at bound ⊢
    simp only [spec.types.lookup, nearest]
    by_cases h : level = spec.types.length _ earlier
    · subst h; simp
    · have lt : level < spec.types.length _ earlier := by omega
      have eq : spec.types.length _ earlier + 1 - 1 - level =
          (spec.types.length _ earlier - 1 - level) + 1 := by omega
      simp only [Int.natCast_inj, h, if_false, eq, FrenBase.Binding.lookup_older]
      exact ih lt

/-- Arguments and parameters correspond level by level, so their numbers agree. -/
theorem argument_types_length (args : spec.types.Snoc spec.types.Judgment)
    (parameters : spec.types.Snoc spec.types.Ty)
    (h : spec.types.argument_types? args parameters = true) :
    spec.types.length _ args = spec.types.length _ parameters := by
  induction args generalizing parameters with
  | Empty =>
    cases parameters with
    | Empty => rfl
    | Extend _ _ => simp [spec.types.argument_types?] at h
  | Extend earlier arg ih =>
    cases parameters with
    | Empty => simp [spec.types.argument_types?] at h
    | Extend earlierParameters parameter =>
      simp only [spec.types.argument_types?, decide_eq_true_eq] at h
      simp [spec.types.length, ih earlierParameters h.2]

/-- Every arm found at a level satisfies the per-arm rule. -/
theorem arms_each (s : spec.types.Snoc spec.types.Entry)
    (arms : spec.types.Snoc (spec.types.ArmF spec.types.Judgment))
    (owner : Fren.Seq String) (context : spec.types.Snoc spec.types.Ty) (ty : spec.types.Ty)
    (level : Int) (arm : spec.types.ArmF spec.types.Judgment)
    (h : spec.types.arms? s arms owner context ty = true)
    (found : spec.types.lookup _ arms level = some arm) :
    spec.types.arm? s arm owner context ty = true := by
  induction arms with
  | Empty => simp [spec.types.lookup] at found
  | Extend earlier last ih =>
    simp only [spec.types.arms?, decide_eq_true_eq] at h
    simp only [spec.types.lookup] at found
    split at found
    · cases found; simpa [spec.types.arm?] using h.1
    · exact ih h.2 found

/-- Children that satisfy `in_context?` each use the context. -/
theorem children_context (children : spec.types.Snoc spec.types.Judgment)
    (context : spec.types.Snoc spec.types.Ty) (level : Int) (child : spec.types.Judgment)
    (h : spec.types.in_context? children context = true)
    (found : spec.types.lookup _ children level = some child) :
    child.context = context := by
  induction children with
  | Empty => simp [spec.types.lookup] at found
  | Extend earlier last ih =>
    simp only [spec.types.in_context?, decide_eq_true_eq] at h
    simp only [spec.types.lookup] at found
    split at found
    · cases found; exact h.1
    · exact ih h.2 found

/-- Every argument of a typed call, at every level, uses the call's context. -/
theorem call_arguments_context (s : spec.types.Snoc spec.types.Entry)
    (context : spec.types.Snoc spec.types.Ty) (item : Fren.Seq String)
    (args : spec.types.Snoc spec.types.Judgment) (ty : spec.types.Ty)
    (h : spec.types.layer_rule? s context (.Call item args) ty = true)
    (level : Int) (arg : spec.types.Judgment)
    (found : spec.types.lookup _ args level = some arg) :
    arg.context = context := by
  simp [spec.types.layer_rule?, fren_spec] at h
  exact children_context args context level arg h.2.1.2 found

/-- A typed match's scrutinee and every arm body, at every level, use the
match's context, and every arm body has the match's type. -/
theorem match_arms_context (s : spec.types.Snoc spec.types.Entry)
    (context : spec.types.Snoc spec.types.Ty) (scrutinee : spec.types.Judgment)
    (arms : spec.types.Snoc (spec.types.ArmF spec.types.Judgment)) (ty : spec.types.Ty)
    (h : spec.types.layer_rule? s context (.Match scrutinee arms) ty = true) :
    scrutinee.context = context ∧
      ∀ (level : Int) (arm : spec.types.ArmF spec.types.Judgment),
        spec.types.lookup _ arms level = some arm →
          arm.body.context = context ∧ arm.body.ty = ty := by
  cases arms with
  | Empty => simp [spec.types.layer_rule?, fren_spec] at h
  | Extend earlier last =>
    simp [spec.types.layer_rule?, fren_spec] at h
    obtain ⟨hs, _, ⟨hlast, hentry⟩, hrest⟩ := h
    refine ⟨hs, fun level arm found => ?_⟩
    have whole : spec.types.arms? s (.Extend earlier last)
        (match scrutinee.ty with | .Nominal x0 => x0 | _ => default) context ty = true := by
      simp [spec.types.arms?, spec.types.arm?, hlast, hentry, hrest]
    have := arms_each s _ _ context ty level arm whole found
    simp only [spec.types.arm?, decide_eq_true_eq] at this
    exact this.1

/-- Context discipline for every form with children: ordinary children use
the layer's context, a let body extends it by the value's type, and match
arms add no binder. -/
theorem layer_context (s : spec.types.Snoc spec.types.Entry)
    (context : spec.types.Snoc spec.types.Ty) (ty : spec.types.Ty) :
    (∀ op operand, spec.types.layer_rule? s context (.UnaryExpression op operand) ty = true →
      operand.context = context) ∧
    (∀ op left right, spec.types.layer_rule? s context (.BinaryExpression op left right) ty = true →
      left.context = context ∧ right.context = context) ∧
    (∀ item args, spec.types.layer_rule? s context (.Call item args) ty = true →
      ∀ level arg, spec.types.lookup _ args level = some arg → arg.context = context) ∧
    (∀ q value body, spec.types.layer_rule? s context (.Let q value body) ty = true →
      value.context = context ∧ body.context = .Extend context value.ty) ∧
    (∀ condition yes no, spec.types.layer_rule? s context (.Conditional condition yes no) ty = true →
      condition.context = context ∧ yes.context = context ∧ no.context = context) ∧
    (∀ scrutinee arms, spec.types.layer_rule? s context (.Match scrutinee arms) ty = true →
      scrutinee.context = context ∧ ∀ level arm, spec.types.lookup _ arms level = some arm →
        arm.body.context = context) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro op operand h; simp [spec.types.layer_rule?, fren_spec] at h; exact h.1
  · intro op left right h; simp [spec.types.layer_rule?, fren_spec] at h; exact h.1
  · intro item args h level arg found; exact call_arguments_context s context item args ty h level arg found
  · intro q value body h; simp [spec.types.layer_rule?, fren_spec] at h; exact ⟨h.1.1.1, h.1.2⟩
  · intro condition yes no h; simp [spec.types.layer_rule?, fren_spec] at h
    exact ⟨h.1.1.1.1.1, h.1.1.1.2, h.1.2⟩
  · intro scrutinee arms h
    have := match_arms_context s context scrutinee arms ty h
    exact ⟨this.1, fun level arm found => (this.2 level arm found).1⟩

example : spec.types.INTEGER_EXAMPLE := by
  decide

example : spec.types.WRONG_LITERAL_EXAMPLE := by
  decide

example : spec.types.ABSENT_LOCAL_EXAMPLE := by
  decide

example : spec.types.OLDEST_LEVEL_EXAMPLE := by
  decide

example : spec.types.WRONG_LEVEL_EXAMPLE := by
  decide

example : spec.types.NEWEST_LEVEL_EXAMPLE := by
  decide

example : spec.types.MISSING_CHILD_EXAMPLE := by
  decide

example : spec.types.NOMINAL_EQUALITY_EXAMPLE := by
  decide

example : spec.types.DOMAIN_SEPARATE_EXAMPLE := by
  decide

example : spec.types.UNARY_EXAMPLE := by
  decide

example : spec.types.UNARY_REJECT_EXAMPLE := by
  decide

example : spec.types.BINARY_EXAMPLE := by
  decide

example : spec.types.BINARY_REJECT_EXAMPLE := by
  decide

example : spec.types.BOOLEAN_RIGHT_CHECKED_EXAMPLE := by
  decide

example : spec.types.LET_BODY_EXAMPLE := by
  decide

example : spec.types.LET_LEVEL_EXAMPLE := by
  decide

example : spec.types.SUFFIX_EXAMPLE := by
  decide

example : spec.types.LET_VALUE_SCOPE_EXAMPLE := by
  decide

example : spec.types.CONDITIONAL_EXAMPLE := by
  decide

example : spec.types.BOTH_BRANCHES_EXAMPLE := by
  decide

example : spec.types.CONDITION_TYPE_EXAMPLE := by
  decide

example : spec.types.MATCH_ARMS_EXAMPLE := by
  decide

example : spec.types.MATCH_OWNER_EXAMPLE := by
  decide

example : spec.types.MATCH_EMPTY_EXAMPLE := by
  decide

example : spec.types.MATCH_ALL_BODIES_EXAMPLE := by
  decide

example : spec.types.COVERAGE_SEPARATE_EXAMPLE := by
  decide

example : spec.types.DUPLICATES_SEPARATE_EXAMPLE := by
  decide

example : spec.types.CALL_EXAMPLE := by
  decide

example : spec.types.CALL_ARITY_EXAMPLE := by
  decide

example : spec.types.CALL_ARGUMENT_EXAMPLE := by
  decide

example : spec.types.CONSTRUCTOR_NOT_CALLABLE_EXAMPLE := by
  decide

example : spec.types.FUNCTION_NOT_VALUE_EXAMPLE := by
  decide

example : spec.types.CONSTRUCTOR_TYPE_EXAMPLE := by
  decide

example : spec.types.CONTEXT_ALIGNMENT_EXAMPLE := by
  decide

example : spec.types.PARAMETER_ORDER_EXAMPLE := by
  decide

example : spec.types.PARAMETER_SUFFIX_EXAMPLE := by
  decide

example : spec.types.IMPLICIT_BOOLEAN_EXAMPLE := by
  decide

example : spec.types.MISSING_ANNOTATION_EXAMPLE := by
  decide

example : spec.types.EXPLICIT_NOT_OVERWRITTEN_EXAMPLE := by
  decide

example : spec.types.VALUE_OWNER_EXAMPLE := by
  decide

example : spec.types.WRONG_VALUE_OWNER_EXAMPLE := by
  decide

example : spec.types.DIRECT_CALLEE_EXAMPLE := by
  decide

end Spec.Language.Types
