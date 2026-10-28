import Fren.View

open Fren.Lang

mod boolean_member_lint
#guard_msgs in
expect members(x?) {
    expect distinct: or { first: x?, false }
}

-- Declaring this block must not diagnose its distinct members as eq_op.
-- Keep the normal eq_op setting so this tests the source-lint path.
