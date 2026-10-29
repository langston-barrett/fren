import Fren.View

open Fren.Lang

/-- error: expected a nonempty labelled invariant list -/
#guard_msgs in
type Missing = value: Int where and {}

-- fren-covers: lang::subset_labels
