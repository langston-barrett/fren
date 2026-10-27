-- keep-sorted start
import FrenCore.FnBlocks
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # Function blocks (`Reqs/Lang/Items#function-blocks`) -/

namespace Fren.Impls

def toFnMemberKind : Fren.Core.FnMember → lang.FnMemberKind
  | .use => .Use
  | .assumption => .Assumption
  | .exists => .Exists
  | .let => .Let
  | .define => .Define
  | .call => .Call
  | .guarantee => .Guarantee
  | .claim => .Claim
  | .evidence => .Evidence

def toFnVerdict : Fren.Core.FnVerdict → lang.FnVerdict
  | .accepted => .Accepted
  | .notFunctions => .NotFunctions
  | .notYet => .NotYet

-- For every member of a function's block, written `det` or not: whether
-- the block takes it, as both front ends decide it.
impl fn_member: lang::fn_member for (m : Fren.Core.FnMember) (d : Bool) {
  member := toFnMemberKind m,
  det? := d,
  verdict := toFnVerdict (Fren.Core.fnMemberVerdict m d),
} by
  intro m d _
  cases m <;> cases d <;> simp [fren_spec, toFnMemberKind, toFnVerdict, Fren.Core.fnMemberVerdict]

end Fren.Impls
