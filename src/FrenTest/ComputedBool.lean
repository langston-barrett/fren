-- keep-sorted start
import Fren.Elab
-- keep-sorted end

open Fren.Lang
mod computed_bool

set_option fren.lint.undecidable "allow" in
proc membership(values: Seq<Bool>): (present?) {
  out present? := false in values
}
proc nonnegative(value: Int): (accepted?) {
  out accepted? := value >= 0
}

-- Kernel reduction checks the actual generated Boolean outputs. A classical
-- decision here would make these proofs stick, even though the propositions
-- are decidable over ordinary finite data.
example : Fren.Generated.computed_bool.membership.out.present? (Fren.Seq.ofList [true, false]) = true := by
  decide +kernel
example : Fren.Generated.computed_bool.membership.out.present? (Fren.Seq.ofList [true]) = false := by
  decide +kernel
example : Fren.Generated.computed_bool.nonnegative.out.accepted? (0 : Int) = true := by
  decide +kernel
example : Fren.Generated.computed_bool.nonnegative.out.accepted? (-1 : Int) = false := by
  decide +kernel

-- Native compilation must also work; this is independent of kernel reduction.
#guard Fren.Generated.computed_bool.membership.out.present? (Fren.Seq.ofList [false])
#guard !Fren.Generated.computed_bool.nonnegative.out.accepted? (-2 : Int)
