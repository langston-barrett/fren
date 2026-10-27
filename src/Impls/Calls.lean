-- keep-sorted start
import Impls.Check
import Reqs.Calls
-- keep-sorted end
open Fren.Lang

/-! # Calls (`Reqs/Calls`) -/

namespace Fren.Impls

open Fren.Core (CallArity Place Role callArity callBindings checkMention)

instance : Fren.Finite Place := ⟨[.assume, .binding, .prop, .argument], by intro x; cases x <;> simp⟩
instance : Fren.Finite Role :=
  ⟨[.input, .output, .instInput, .instOutput, .instHidden], by intro x; cases x <;> simp⟩

def toPlace : Place → call.Place
  | .assume => .Assume
  | .binding => .CallArg
  | .prop => .Constraint
  | .argument => .FnArg

def toRole : Role → call.Role
  | .input => .Input
  | .output => .Output
  | .instInput => .CallInput
  | .instOutput => .CallOutput
  | .instHidden => .CallHidden

impl mention: call::mention for (p : Place) (r : Role) (earlier : Bool) {
  place := toPlace p,
  role := toRole r,
  earlier? := earlier,
  allowed? := (checkMention p r earlier `w.x).isOk,
}

def toArity : CallArity → call.Arity
  | .fits => .Fits
  | .tooMany => .TooMany
  | .tooFew => .TooFew

interp call::VarName := String
interp call::Arg := Nat

/-- What a call with the arguments `as`, of a procedure with the
parameters `ps`, binds at position `k`, as both front ends and the
evaluator bind it (`Core.callBindings`). -/
def boundAt (ps : List String) (as : List Nat) (k : Int) : Option (String × Nat) :=
  if 0 ≤ k then (callBindings ps.toArray as.toArray).bind (·[k.toNat]?) else none

-- For every call, at every position.
impl arguments: call::arguments for (ps : List String) (as : List Nat) (k : Int) {
  params := Fren.Seq.ofList ps,
  args := Fren.Seq.ofList as,
  k := k,
  arity := toArity (callArity ps.length as.length),
  binds? := (boundAt ps as k).isSome,
  param := ((boundAt ps as k).map (·.1)).getD default,
  arg := ((boundAt ps as k).map (·.2)).getD default,
} by
  intro ps as k _
  have hk : ∀ (l : List String) (m : List Nat), boundAt l m k =
      if 0 ≤ k ∧ m.length = l.length ∧ k < l.length then some (l[k.toNat]!, m[k.toNat]!) else none := by
    intro l m
    unfold boundAt callBindings callArity
    by_cases h0 : 0 ≤ k
    · by_cases hl : m.length = l.length
      · by_cases h1 : k < l.length
        · have h1' : k.toNat < l.length := by omega
          simp [h0, hl, h1, h1']
        · simp [h0, hl, h1]
      · simp [h0, hl]
        split <;> simp
    · simp [h0]
  rw [hk]
  unfold callArity toArity
  by_cases h0 : 0 ≤ k <;> by_cases hl : as.length = ps.length <;> by_cases h1 : k < ps.length
    <;> simp [fren_spec, h0, hl, h1, Fren.Seq.nth, Int.ofNat_inj]
    <;> first | omega | (by_cases hg : ps.length < as.length <;> simp [hg] <;> omega) | skip

end Fren.Impls
