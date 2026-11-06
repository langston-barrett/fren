-- keep-sorted start
import Impls.Check
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

impl function_params: lang::function_params for (d c : Bool) (p n : Nat) {
  defined? := d,
  contract? := c,
  n_params := p,
  n_named := n,
  accepted? := Fren.Core.functionParamsAccepted d c p n,
} by
  intro d c p n _
  cases d <;> cases c <;> simp [fren_spec, Fren.Core.functionParamsAccepted] <;> omega

def toClauseKind : Fren.Core.ClauseKind → lang.ClauseKind
  | .precondition => .Precondition
  | .postcondition => .Postcondition

instance : Fren.Finite Fren.Core.ClauseKind := ⟨[.precondition, .postcondition], by intro x; cases x <;> simp⟩

-- For every clause and application: the rule that both front ends call at
-- each application of the function itself in its contract.
impl contract_application: lang::contract_application for (k : Fren.Core.ClauseKind) (o t : Bool) {
  clause := toClauseKind k,
  own? := o,
  to_params? := t,
  accepted? := Fren.Core.contractApplicationAccepted k o t,
}

/-- An argument as both front ends read it (`Core.appliesToParams`): a
parameter's name, or any other expression. -/
def writtenName? : lang.Written → Option Lean.Name
  | .Name .P0 => some `p0
  | .Name .P1 => some `p1
  | .Name .P2 => some `p2
  | .Other => none

/-- A parameter's name; `Other` is never one, and its name no argument's. -/
def paramName : lang.Written → Lean.Name
  | .Name .P0 => `p0
  | .Name .P1 => `p1
  | .Name .P2 => `p2
  | .Other => `«#other»

theorem writtenName_beq (a p : lang.Written) :
    (writtenName? a == some (paramName p)) = (decide (a = p) && !decide (p = .Other)) := by
  rcases a with ⟨_ | _ | _⟩ | _ <;> rcases p with ⟨_ | _ | _⟩ | _ <;> decide

theorem appliesToParams_iff (as ps : List lang.Written) :
    Fren.Core.appliesToParams (as.toArray.map writtenName?) (ps.toArray.map paramName)
      = (decide (as = ps) && !decide (lang.Written.Other ∈ ps)) := by
  simp only [Fren.Core.appliesToParams, Array.toList_map, List.map_map]
  induction as generalizing ps with
  | nil => cases ps <;> simp
  | cons a as ih =>
    cases ps with
    | nil => simp
    | cons p ps =>
      simp only [List.map_cons, List.cons_beq_cons, Function.comp_apply, writtenName_beq, ih, List.cons.injEq,
        List.mem_cons]
      by_cases h1 : a = p <;> by_cases h2 : p = .Other <;> by_cases h3 : as = ps <;>
        by_cases h4 : lang.Written.Other ∈ ps <;> simp [h1, h2, h3, h4, eq_comm]

-- For every application of the function in its own contract, of up to
-- three parameters: the rule that both front ends call, on the arguments
-- as they read them.
impl contract_arguments: lang::contract_arguments for (k : Fren.Core.ClauseKind) (o : Bool) (ps as : List lang.Written) {
  clause := toClauseKind k,
  own? := o,
  params := Fren.Seq.ofList ps,
  args := Fren.Seq.ofList as,
  accepted? := Fren.Core.contractApplicationAccepted k o
    (Fren.Core.appliesToParams (as.toArray.map writtenName?) (ps.toArray.map paramName)),
} by
  intro k o ps as _
  rw [appliesToParams_iff]
  cases k <;> cases o <;> simp [fren_spec, toClauseKind, Fren.Core.contractApplicationAccepted, Fren.Seq.ext_iff] <;>
    first | (intro h; exact absurd h (by decide)) | (intros; rfl)

end Fren.Impls
