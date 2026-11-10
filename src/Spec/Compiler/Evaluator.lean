import Fren.Impl
import Fren.Literate
import FrenEval
import Spec.Compiler.Thir

open Fren.Lang

#fren_md "Evaluator.md"

-- Laws refer to the actual interpreter and producer, not an executable spec IR.
#check FrenEval.Program.retains
#check FrenEval.Program.static
#check FrenEval.fromResolved_success
#check FrenEval.binary_add
#check FrenEval.binary_sub
#check FrenEval.binary_mul
#check FrenEval.binary_div
#check FrenEval.binary_mod
#check FrenEval.div_zero
#check FrenEval.mod_zero
#check FrenEval.euclidean
#check FrenEval.evaluate_selected
#check FrenEval.evaluate_type
#check FrenEval.evaluate_deterministic

namespace Spec.Compiler.Evaluator

-- Only finite operator tags are adapted; demand is decided in the walker helper.
def booleanOp : spec.evaluator.BooleanOp → FrenAst.BinaryOp
  | .And => .and | .Or => .or | .Iff => .iff | .Equal => .eq | .NotEqual => .ne

impl right_demand: right_demand for (op : spec.evaluator.BooleanOp) (left? : Bool) {
  op := op, left? := left?,
  needed? := (FrenEval.shortCircuit (booleanOp op) (.bool left?)).isNone
} by
  intro op left _
  cases op <;> cases left <;> simp [fren_spec, booleanOp, FrenEval.shortCircuit]

#check FrenEval.walk_and_false
#check FrenEval.walk_or_true
#check FrenEval.walk_let
#check FrenEval.walk_local
#check FrenEval.walk_strict_failure
#check FrenEval.shortCircuit_strict

-- These expectations test actual traversal, beyond the primitive impl.
-- Values come from Language.
private def source := "mod demand\n\
  fn unused(dummy: Int): Int := let x := 1 div 0 in 0\n\
  fn used(dummy: Int): Int := let x := 1 div 0 in x\n\
  fn conjunction(b?: Bool): Bool := b? and (1 div 0 = 0)\n\
  fn disjunction(b?: Bool): Bool := b? or (1 % 0 = 0)"

#guard match FrenEval.fromSource ⟨703⟩ source with
  | .error _ => false
  | .ok p => Id.run do
    for (name, args, expected) in [("unused", #[FrenEval.Value.int 0], FrenEval.Value.int 0),
        ("conjunction", #[.bool false], .bool false), ("disjunction", #[.bool true], .bool true)] do
      let key := FrenBase.ItemId.root.named "demand" |>.named name
      let .ok e := FrenEval.evaluate p ⟨key, none⟩ args 100 | return false
      let .ok actual := e.outcome | return false
      if actual != expected then return false
    for (name, args) in [("used", #[FrenEval.Value.int 0]),
        ("conjunction", #[.bool true]), ("disjunction", #[.bool false])] do
      let key := FrenBase.ItemId.root.named "demand" |>.named name
      let .ok e := FrenEval.evaluate p ⟨key, none⟩ args 100 | return false
      let .error (.undefined ..) := e.outcome | return false
    return true

open spec.evaluator in
interp evaluator_pick := fun arms c => Spec.Compiler.Thir.pickArm arms c

open spec.evaluator in
impl evaluator_selection_proof: evaluator_selection for
    (arms : spec.surface.Snoc (spec.names.ArmF spec.types.Typing)) (constructor : Fren.Seq String) {
  arms := arms, constructor := constructor, holds? := true
} by
  intro arms constructor _
  simp only [evaluator_selection.ensures, evaluator_selection.ensure.output,
    evaluator_selection.ensure.agrees, evaluator_pick]
  exact ⟨trivial, Spec.Compiler.Thir.pickArm_eq_select arms constructor⟩

end Spec.Compiler.Evaluator

#fren_check evaluator_selection
