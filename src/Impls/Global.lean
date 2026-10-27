-- keep-sorted start
import FrenCore.Global
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # Global expectations, and the migration from `forall` (`Reqs/Lang/Global`) -/

namespace Fren.Impls

open Fren.Core (BlockMember blockMemberAccepted)

def toBlockMember : BlockMember → lang.BlockMember
  | .result => .Result
  | .exists => .Exists
  | .let => .Let
  | .define => .Define
  | .assume => .Assume
  | .ensure => .Ensure
  | .expect => .Expect
  | .cover => .Cover
  | .call => .Call
  | .use => .Use

-- For every member, `det` or not: whether a global expectation's block
-- accepts it, as both front ends decide.
impl block_member: lang::block_member for (m : BlockMember) (d : Bool) {
  member := toBlockMember m,
  «det?» := d,
  «accepted?» := blockMemberAccepted m d,
} by
  intro m d
  cases m <;> cases d <;> simp [fren_spec, toBlockMember, blockMemberAccepted]

end Fren.Impls
