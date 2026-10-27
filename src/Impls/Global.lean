-- keep-sorted start
import FrenCore.Global
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # Global expectations, and the migration from `forall` (`Reqs/Lang/Global`) -/

namespace Fren.Impls

open Fren.Core (BlockMember Callee blockMemberAccepted calleeFixable migratedParam)

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

def toCallee (c : Callee) : lang.Callee :=
  { module := c.module, «closed?» := c.closed }

-- For every module and procedure: whether the fix of an old global
-- expectation can copy the procedure's text.
impl callee_fix: lang::callee_fix for (md : String) (c : Callee) {
  module := md,
  callee := toCallee c,
  «fixable?» := calleeFixable md c,
} by
  intro md c
  simp [fren_spec, toCallee, calleeFixable]

-- For every binder, parameter and set of taken names: the name that the
-- fix declares, and whether it is fresh.
impl migrated_param: lang::migrated_param for (w p : String) (taken : Fren.FinSet String) {
  binder := w,
  param := p,
  taken := taken,
  name := migratedParam w p,
  «fresh?» := decide (migratedParam w p ∉ taken),
} by
  intro w p taken
  simp [fren_spec, migratedParam]

end Fren.Impls
