-- keep-sorted start
import FrenCore.Global
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # Global expectations (`Reqs/Lang/Global`) -/

namespace Fren.Impls

open Fren.Core (BlockMember PreconditionWord assumeRenamedMsg requireInGlobalMsg blockMemberAccepted blockMemberMsg blockMemberReport?
  preconditionKeyword preconditionReport?)

def toBlockMember : BlockMember → lang.BlockMember
  | .result => .Result
  | .exists => .Exists
  | .let => .Let
  | .define => .Define
  | .assume => .Assume
  | .require => .Require
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

def toPreconditionWord : PreconditionWord → lang.PreconditionWord
  | .require => .Require
  | .assume => .Assume

/-- What a front end reports for a clause, by its message's code
(`lang::PreconditionReport`). -/
def toPreconditionReport : Option Fren.Core.Msg → lang.PreconditionReport
  | some msg => if msg.code? = some "F0169" then .F0169 else if msg.code? = some "F0417" then .F0417 else .NoReport
  | none => .NoReport

-- For each word and block: the keyword that messages name the block's
-- assumptions by, and the code of what both front ends report for a
-- clause that starts with the word, with `preconditionReport?`: `F0169`
-- or `F0417`, once the item is read, if it has no error of its syntax.
impl precondition_word: lang::precondition_word for (w : PreconditionWord) (g : Bool) {
  word := toPreconditionWord w,
  «global?» := g,
  keyword := preconditionKeyword g,
  report := toPreconditionReport (preconditionReport? g w),
} by
  intro w g
  cases w <;> cases g <;> simp [fren_spec, toPreconditionWord, preconditionKeyword, preconditionReport?, assumeRenamedMsg,
    requireInGlobalMsg, toPreconditionReport]

end Fren.Impls
