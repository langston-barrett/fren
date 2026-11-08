import Fren.Impl
import Fren.Literate
import FrenEval

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
