-- keep-sorted start
import FrenCli.MatchDisjoint
import FrenCli.Parse
import Reqs.Cli
-- keep-sorted end

open Fren.Lang

namespace Fren.Impls.MatchDisjoint

open Fren.Core (Pat PatTy)

/-- Only the immediate field's syntax class is abstracted; no omission
or disjointness result is supplied to the requirement. -/
def field : Pat → cli.MatchQueryField
  | .wild false => .Wildcard
  | .wild true => .Binder
  | _ => .Test

def pattern : Pat → cli.MatchQueryPattern
  | .ctor index fields => .Constructor index (Fren.FinSet.ofList (fields.toList.map field))
  | _ => .Other

def kind : PatTy → cli.MatchQueryType
  | .enum path _ => if path == Fren.Core.matchVectorPath then .Vector else .Datatype
  | _ => .Other

def arm {α : Type} (p : Pat × Option α) : cli.MatchQueryArm :=
  { pattern := pattern p.1, «guarded?» := p.2.isSome }

private theorem field_test (p : Pat) :
    field p ≠ cli.MatchQueryField.Test ↔ (match p with | .wild _ => true | _ => false) = true := by
  cases p <;> simp [field]
  case wild b => cases b <;> decide

private theorem constructor_eq (p : Pat) :
    cli.match_query_constructor (pattern p) = (FrenCli.plainMatchConstructor? p).map Int.ofNat := by
  cases p <;> try rfl
  case ctor index fields =>
    have h : cli.MatchQueryField.Test ∉ Fren.FinSet.ofList (fields.toList.map field) ↔
        fields.all (fun p => match p with | .wild _ => true | _ => false) = true := by
      rw [Array.all_eq_true']
      simp only [Fren.FinSet.mem_ofList, List.mem_map, not_exists, not_and,
        Array.mem_toList_iff, field_test]
    by_cases hf : fields.all (fun p => match p with | .wild _ => true | _ => false) = true
    · have hn := h.mpr hf
      simp [pattern, cli.match_query_constructor, cli.MatchQueryPattern.Constructor.x0,
        cli.MatchQueryPattern.Constructor.x1, FrenCli.plainMatchConstructor?, hn]
      exact Array.all_eq_true.mp hf
    · have hn : cli.MatchQueryField.Test ∈ Fren.FinSet.ofList (fields.toList.map field) := by
        exact Classical.byContradiction fun hn => hf (h.mp hn)
      simp [pattern, cli.match_query_constructor, cli.MatchQueryPattern.Constructor.x0,
        cli.MatchQueryPattern.Constructor.x1, FrenCli.plainMatchConstructor?, hn]
      obtain ⟨i, hi, bad⟩ := Array.all_eq_false.mp (Bool.eq_false_iff.mpr hf)
      exact ⟨i, hi, Bool.eq_false_iff.mpr bad⟩

impl match_exclusions: cli::match_exclusions for (ty : PatTy) (p : Pat)
    (guard : Option FrenCli.Expr) (previous : Array (Pat × Option FrenCli.Expr)) {
  kind := kind ty,
  current := arm (p, guard),
  earlier := Fren.FinSet.ofList (previous.toList.map arm),
  omit? := FrenCli.omitMatchExclusions ty p guard previous,
} by
  intro ty p guard previous _
  change cli.match_exclusions.ensure.policy (kind ty) (arm (p, guard))
    (Fren.FinSet.ofList (previous.toList.map arm)) (FrenCli.omitMatchExclusions ty p guard previous)
  unfold cli.match_exclusions.ensure.policy
  simp only [arm, Fren.FinSet.mem_ofList, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂]
  simp only [constructor_eq]
  cases ty <;> cases guard <;> try (solve | simp [kind, FrenCli.omitMatchExclusions])
  case enum.none path args =>
    cases h : FrenCli.plainMatchConstructor? p with
    | none => simp [kind, FrenCli.omitMatchExclusions, h]
    | some index =>
      simp [kind, FrenCli.omitMatchExclusions, h, Fren.Prelude.Option.some.x0]
      intro _
      refine (Array.forall_mem_iff_forall_getElem (xs := previous)
        (P := fun q => q.2 = none ∧
          (FrenCli.plainMatchConstructor? q.1).any (· != index) = true)).symm.trans ?_
      simp only [Prod.forall]
      apply forall_congr' fun a => ?_
      apply forall_congr' fun b => ?_
      apply forall_congr' fun _ => ?_
      cases FrenCli.plainMatchConstructor? a <;>
        simp [Int.ofNat_inj]

end Fren.Impls.MatchDisjoint
