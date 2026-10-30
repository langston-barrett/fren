-- keep-sorted start
import FrenCore.Global
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # Global expectations (`Reqs/Lang/Global`) -/

namespace Fren.Impls

open Fren.Core (BlockMember blockMemberAccepted blockMemberMsg blockMemberReport?)

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
  | .refines => .Refines
  | .use => .Use

/-- What a front end reports for a member, by its message's code
(`lang::MemberReport`): an error with another code is none of the spec's. -/
def toMemberReport : Option Fren.Core.Msg → lang.MemberReport
  | some msg => if msg.code? = some "F0417" then .F0417 else .NoReport
  | none => .NoReport

-- For every member, `det` or not: whether a global expectation's block
-- accepts it, as both front ends decide, and the code of what they report
-- for it with `blockMemberReport?`, before any other check of it.
impl block_member: lang::block_member for (m : BlockMember) (d : Bool) {
  member := toBlockMember m,
  «det?» := d,
  «accepted?» := blockMemberAccepted m d,
  report := toMemberReport (blockMemberReport? m d),
} by
  intro m d
  cases m <;> cases d <;> simp [fren_spec, toBlockMember, blockMemberAccepted, blockMemberReport?, blockMemberMsg, toMemberReport]

end Fren.Impls
