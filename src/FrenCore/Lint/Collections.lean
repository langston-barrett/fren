-- keep-sorted start
import FrenCore.Lint.Model
import FrenCore.Mentions
import FrenCore.Simplify
-- keep-sorted end

/-!
# Collection, output and index lints

Part of `FrenCore.Lint`, shared by both front ends.
-/

open Lean

namespace Fren.Core

/-! ## Collections, outputs and indexes -/

/-- `c` with its operands swapped: `a OP b` is `b OP' a`. -/
def Comparison.mirror : Comparison → Comparison
  | .lt => .gt
  | .gt => .lt
  | .le => .ge
  | .ge => .le
  | c => c

/-- Whether `length_zero` and `card_zero` fire on a comparison of a length
`n` with `bound`, `n OP bound` if `lengthLeft` and `bound OP n` otherwise,
and whether the fix says that it is empty (`lint::length_zero`). -/
def lengthZero (op : Comparison) (bound : Int) (lengthLeft : Bool) : Bool × Bool :=
  match if lengthLeft then op else op.mirror with
  | .eq | .le => (bound == 0, true)
  | .ne | .gt => (bound == 0, false)
  | .lt => (bound == 1, true)
  | .ge => (bound == 1, false)

/-- Whether `absurd_extreme_comparisons` fires on a comparison of a length
`n` with `bound`, `n OP bound` if `lengthLeft` and `bound OP n` otherwise,
and what it always is (`lint::absurd_extreme_comparisons`): `n` is never
negative, so it is above `bound`, or, for `0`, the same or above. -/
def absurdComparison (op : Comparison) (bound : Int) (lengthLeft : Bool) : Bool × Bool :=
  match if lengthLeft then op else op.mirror with
  | .lt => (bound ≤ 0, false)
  | .ge => (bound ≤ 0, true)
  | .eq | .le => (bound < 0, false)
  | .ne | .gt => (bound < 0, true)

/-- A comparison of a `len`, or a `card` if `card`, that is always `value`. -/
def absurdComparisonMsg (card value : Bool) : Msg :=
  { code? := some Lint.absurdExtremeComparisons.code, headline := s!"this comparison is always `{value}`"
    label? := some s!"`{if card then "card" else "len"}` is never negative"
    notes := #["note: the bound or the operator is probably not the one meant"] }

/-- `x in {a}`, as the texts of `x` and `a`. -/
def singletonMembershipMsg (x a : String) : Msg :=
  { code? := some "F0717", headline := "membership in a set of one member is equality", label? := some "a set of one"
    fixes := #[{ msg := "write it as an equation", replacement := s!"{x} = {a}" }] }

/-- Whether `membership_chain` fires on a chain of `n` operands of `or`, or
of `and`, which all equate, or for `and` disequate, the same left operand if
`sameLeft`, where `laterIndexes` says that a right operand but the first
indexes a sequence, and `patterns` that each right operand is a value that
a pattern writes (`patternValue`), which `manual_pattern_test` then
reports (`lint::membership_chain`). -/
def membershipChainFires (n : Nat) (sameLeft laterIndexes patterns : Bool) : Bool :=
  sameLeft && n ≥ 3 && !laterIndexes && !patterns

/-- `x = a or x = b or ...`, or `x != a and x != b and ...` if `negated`, as
the texts of `x` and the others. -/
def membershipChainMsg (x : String) (vals : Array String) (negated : Bool) : Msg :=
  let set := s!"\{{", ".intercalate vals.toList}}"
  { code? := some "F0718", headline := s!"this is `{x}` {if negated then "not " else ""}in a set of {vals.size}"
    label? := some s!"a chain of `{if negated then "and" else "or"}`"
    fixes := #[{ msg := "write it as a membership"
                 replacement := if negated then s!"not {x} in {set}" else s!"{x} in {set}" }] }

/-- Whether `constant_output` and `definable_output` fire on an output,
where `mentioned` is what its definition mentions, if it is defined
(`lint::output_lints`). -/
def outputLints (defined : Bool) (mentioned : List Mention) (nReqs : Nat) (equation : Bool) : Bool × Bool :=
  (defined && mentioned.isEmpty, !defined && nReqs == 1 && equation)

def constantOutputMsg (x : Name) : Msg :=
  { code? := some "F0719", headline := s!"defined output `{x}` is the same in every behaviour"
    label? := some "mentions no variable"
    notes := #["help: make it a `const`, which is shared by every procedure"] }

def definableOutputMsg (x : Name) (req : Name) : Msg :=
  { code? := some "F0720", headline := s!"`{req}` could be the definition of `{x}`"
    label? := some "constrained by one equation"
    notes := #[s!"help: write the expression as `{x}`'s definition, `out {x} := ...`, and remove `{req}`"] }

/-- Whether `index_after_use` fires (`lint::index_after_use`). -/
def indexAfterUse (indexesLeft boundsRight : Bool) : Bool := indexesLeft && boundsRight

/-- `a and b`, as their texts, where `b` bounds what `a` indexes. -/
def indexAfterUseMsg (a b : String) : Msg :=
  { code? := some "F0721", headline := "the bound comes after the index it guards", label? := some "indexed before it is bounded"
    notes := #["note: in `a and b`, `b` is guarded by `a`, not the other way around, so the index may be out of range"]
    fixes := #[{ msg := "put the bound first, which does not change the meaning", replacement := s!"{b} and {a}" }] }

end Fren.Core
