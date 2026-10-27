-- keep-sorted start
import FrenCore.Global
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

/-! # Global expectations, and the migration from `forall` (`Reqs/Lang/Global`) -/

namespace Fren.Impls

open Fren.Core (BlockMember Callee CalleeFix Copied blockMemberAccepted calleeFix migratedParam)

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

def toCopied (c : Copied) : lang.Copied :=
  { names := Fren.FinSet.ofArray c.names, bangs := Fren.FinSet.ofArray c.bangs }

def toCallee (c : Callee) : lang.Callee :=
  { module := c.module, params := Fren.FinSet.ofArray c.params, others := Fren.FinSet.ofArray c.others
    types := toCopied c.types, assumes := toCopied c.assumes }

def toCalleeFix : CalleeFix → lang.CalleeFix
  | .fixable => .Fixable
  | .otherModule => .OtherModule
  | .notClosed => .NotClosed
  | .captured => .Captured

theorem any_contains_iff (a b : Array String) : (a.any b.contains = true) ↔ ∃ x, x ∈ a ∧ x ∈ b := by
  constructor
  · intro h
    obtain ⟨x, hx, hc⟩ := Array.any_eq_true'.1 h
    exact ⟨x, hx, by simpa using hc⟩
  · rintro ⟨x, hx, hb⟩
    exact Array.any_eq_true'.2 ⟨x, hx, by simpa using hb⟩

theorem any_captured_iff (ns ms ps bs : Array String) :
    ((ns ++ ms).any (fun n => !ps.contains n && bs.contains n) = true) ↔
      ∃ x, (x ∈ ns ∨ x ∈ ms) ∧ x ∉ ps ∧ x ∈ bs := by
  constructor
  · intro h
    obtain ⟨x, hx, hc⟩ := Array.any_eq_true'.1 h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    exact ⟨x, by simpa using hx, by simpa using hc.1, by simpa using hc.2⟩
  · rintro ⟨x, hx, hp, hb⟩
    exact Array.any_eq_true'.2 ⟨x, by simpa using hx, by simp [hp, hb]⟩

-- For every module, block and procedure: whether the fix of an old global
-- expectation can copy the procedure's text, and if not, why.
impl callee_fix: lang::callee_fix for (md : String) (block : Array String) (c : Callee) {
  module := md,
  block := Fren.FinSet.ofArray block,
  callee := toCallee c,
  fix := toCalleeFix (calleeFix md block c),
} by
  intro md block c _
  simp only [fren_spec, toCallee, toCopied, Fren.FinSet.mem_ofArray, ← any_contains_iff]
  unfold calleeFix
  cases c.assumes.names.any c.others.contains <;> cases c.assumes.bangs.any c.params.contains <;>
    cases h3 : (c.types.names ++ c.assumes.names).any (fun n => !c.params.contains n && block.contains n) <;>
    by_cases hm : c.module = md <;> simp [hm, toCalleeFix]
  all_goals first
    | exact (any_captured_iff _ _ _ _).1 h3
    | intro x hx hp hb; have := (any_captured_iff _ _ _ _).2 ⟨x, hx, hp, hb⟩; rw [h3] at this; cases this

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
