-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-! ## Strings and decidability (`Reqs/Lang/Types#strings`, `Reqs/Lang/Decidability`) -/

impl string_char: lang::string_char for (c : Nat) {
  code := c,
  accepted? := Fren.Core.stringCharAccepted c,
} by
  intro c _
  simp [fren_spec, Fren.Core.stringCharAccepted, Fren.Core.maxChar]

-- With the pattern parser, which both front ends use.
impl char_range: lang::char_range for (lo hi : Int) {
  low := lo,
  high := hi,
  accepted? := Fren.Core.charRangeAccepted lo hi,
} by
  intro lo hi _
  simp [fren_spec, Fren.Core.charRangeAccepted]

instance : Fren.Finite Fren.Core.Method :=
  ⟨Fren.Core.Method.all.toList, by intro x; cases x <;> simp [Fren.Core.Method.all]⟩

def toMethod : Fren.Core.Method → lang.Method
  | .len => .Len
  | .startsWith => .StartsWith
  | .endsWith => .EndsWith
  | .contains => .Contains
  | .matches => .Matches
  | .at => .At
  | .slice => .Slice
  | .indexOf => .IndexOf
  | .replace => .Replace
  | .replaceAll => .ReplaceAll
  | .card => .Card
  | .inverse => .Inverse
  | .closure => .Closure
  | .image => .Image
  | .domain => .Domain
  | .range => .Range
  | .update => .Update
  | .rev => .Rev
  | .abs => .Abs
  | .min => .Min
  | .max => .Max

-- The table of methods that both front ends use, where `o` says that the
-- receiver is of an ordered type other than a number.
impl method_type: lang::method_type for (m : Fren.Core.Method) (k : lang.ValueType) (o : Bool) {
  method := toMethod m,
  receiver := k,
  ordered? := o,
  accepted? := m.accepts (k == .StringTy) (k == .SetTy) (k == .RelTy) (k == .SeqTy) (k == .IntTy || k == .NatTy) o,
  -- `string` is the receiver's type, and `elem` is never a result; the
  -- `min` and `max` of another ordered type give the receiver's type, as
  -- both front ends' `callMethod` does.
  result := if o && (m matches .min | .max) then k else match m.result with
    | .bool => .BoolTy | .int => .IntTy | .string | .elem => k | .set => .SetTy | .rel => .RelTy,
  n_params := m.arity,
} by
  intro m k o _
  cases m <;> cases k <;> cases o <;> simp [fren_spec, toMethod, Fren.Core.Method.accepts, Fren.Core.Method.relational,
    Fren.Core.Method.result,
    Fren.Core.Method.arity, Fren.Core.Method.params]

end Fren.Impls
