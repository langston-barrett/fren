-- keep-sorted start
import Fren.Trace
import Fren.View
-- keep-sorted end

open Fren.Lang

-- Hosted parity for named obligations and short-circuit Boolean blocks.
-- The unbounded alias remains its underlying Int in Lean.
mod boolean_subsets_test
set_option fren.lint.assertions_on_constants "allow"
set_option fren.lint.constant_output "allow"
set_option fren.lint.eq_op "allow"

type Even = n: Int where invariant: n mod 2 = 0
proc plus_two(n: Even): (r: Even) { out r := n + 2 }

type Byte = n: Int where low: n >= 0 and high: n <= 255
proc byte_identity(n: Byte): (r: Byte) { out r := n }

fn healthy?(x?, y?) := and { first: x?, second: y? }
fn some?(x?, y?) := or { first: x?, second: y? }

expect blocks(values: Seq<Int>, x?, y?) {
    expect empty_and: and { }
    expect empty_or: not or { }
    expect iff_singleton: iff { values[0] = 0 }
    expect no_parity: not one { true, true, true }
    expect empty_one: not one { }
    expect singleton_one: one { true }
    expect skip_after_second: not one { true, true, values[0] = 0 }
    expect implication: healthy?(x?, y?) iff (x? and y?)
    expect alternatives: some?(x?, y?) iff (x? or y?)
    expect quantified: forall (b?: Bool), b? iff b?
    expect guarded_quantifier: when x?, forall (b?: Bool), b? iff b?
    expect one_guard: when not x?, one { first: x?, second: not x? }
    expect named: when x? and y?, healthy?(x?, y?)
    expect repeated: when x? and y?, healthy?(x?, y?) and healthy?(y?, x?)
    expect negative: when not x? and not y?, not some?(x?, y?)
}

-- `one` remains an ordinary contextual identifier.
proc identity(one: Int): (r: Int) { out r := one }

#fren_check
