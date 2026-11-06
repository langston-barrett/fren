-- keep-sorted start
import Impls.Check
import Impls.Lang.GenericFunctions
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

interp lang::instantiated := fun (t : Fren.Core.Ty) (as : Fren.Seq Fren.Core.Ty) => t.subst as.toList.toArray

-- For every declared result type and every application's type arguments:
-- the type that the `fren` command gives the application (`Core.callType`).
impl call_instance: lang::call_instance for (result : Fren.Core.Ty) (args : List Fren.Core.Ty) {
  result := result,
  arguments := Fren.Seq.ofList args,
  result_type := Fren.Core.callType result args.toArray,
} by
  intro result args _
  simp [fren_spec, Fren.Core.callType, Fren.Core.genericMorphism]

/-- At type arguments none of which is a `Nat`, as inferred ones are
widened, an instance's result type is a `Nat` exactly when the declared
one is (`Core.instanceNat`). -/
theorem subst_nat_iff (args : Array Fren.Core.Ty) (h : ∀ a ∈ args, a ≠ .nat) (t : Fren.Core.Ty) :
    t.subst args = .nat ↔ t = .nat := by
  cases t with
  | param k n =>
    simp only [Fren.Core.Ty.subst, reduceCtorEq, iff_false]
    cases ha : args[k]? with
    | none => simp
    | some a => exact h a (Array.mem_of_getElem? ha)
  | _ => simp [Fren.Core.Ty.subst]

/-- The first `d` of `ts`, an application's type arguments or a function's
parameters' declared types (`firstTys`), as an array. -/
abbrev firstArr (d : Fin 4) (ts : Fin 3 → Fren.Core.Ty) : Array Fren.Core.Ty := (firstTys d ts).toArray

-- For every function with at most three parameters, every declared result
-- type, with its patterns, and every application of it with at most three
-- type arguments: the sorts of the instance's unknown function, the type
-- whose constraint its applications bring, and whether they are at least
-- 0, as both front ends give them (`Core.instanceSig`, `Core.instanceResult`,
-- `Core.instanceNat`).
impl uninterpreted_instance: lang::uninterpreted_instance
    for (d : Fin 4) (ts : Fin 3 → Fren.Core.Ty) (rp : Fren.Core.PTy) (na : Fin 4) (as : Fin 3 → Fren.Core.Ty) {
  declared := Fren.Seq.ofList (firstTys d ts),
  result := rp.ty,
  arguments := Fren.Seq.ofList (firstTys na as),
  params := Fren.Seq.ofList (Fren.Core.instanceSig (firstArr d ts) rp.ty (firstArr na as)).1.toList,
  result_type := (Fren.Core.instanceSig (firstArr d ts) rp.ty (firstArr na as)).2,
  fact_type := (Fren.Core.instanceResult rp (firstArr na as)).ty,
  nat? := Fren.Core.instanceNat rp.ty,
} by
  intro d ts rp na as hw
  have hfact : (Fren.Core.instanceResult rp (firstArr na as)).ty = rp.ty.subst (firstArr na as) := rfl
  have hk (t : Fren.Core.Ty) : kindOf t = lang.ValueType.NatTy ↔ t = .nat := by cases t <;> simp [kindOf]
  simp only [fren_spec, Fren.Seq.ext_iff, hk] at hw ⊢
  -- The type arguments are not `Nat`s, as the assumption says.
  have hargs : ∀ a ∈ firstArr na as, a ≠ .nat := by
    obtain ⟨_ | _ | _ | _ | na, hna⟩ := na <;> first | omega | skip
    all_goals simp_all [firstArr, firstTys, List.ofFn_succ, Fren.Seq.nth_of_lt]
  refine ⟨⟨?_, by simp [Fren.Core.instanceSig, Fren.Core.genericMorphism, firstArr]⟩, ?_⟩
  · obtain ⟨_ | _ | _ | _ | d, hd⟩ := d <;> first | omega | skip
    all_goals simp [Fren.Core.instanceSig, Fren.Core.genericMorphism, firstArr, firstTys, List.ofFn_succ, Fren.Seq.nth_of_lt]
  · simp only [hfact, Fren.Core.instanceSig, Fren.Core.genericMorphism, Fren.Core.instanceNat, subst_nat_iff _ hargs, beq_iff_eq]
    simp

-- For every application with at most three type arguments, within an
-- instance with any type arguments: the instance it applies, as both front
-- ends find it (`Core.instantiatedArgs`, which `Core.appliedInstance` gives
-- once the function's type parameters are `Ty.param`s).
impl applied_instance: lang::applied_instance for (d : Fin 4) (ts : Fin 3 → Fren.Core.Ty) (outer : List Fren.Core.Ty) {
  inner := Fren.Seq.ofList (firstTys d ts),
  outer := Fren.Seq.ofList outer,
  applied := Fren.Seq.ofList (Fren.Core.instantiatedArgs outer.toArray (firstArr d ts)).toList,
} by
  intro d ts outer _
  simp only [fren_spec, Fren.Seq.ext_iff]
  obtain ⟨_ | _ | _ | _ | d, hd⟩ := d <;> first | omega | skip
  all_goals simp [Fren.Core.instantiatedArgs, Fren.Core.genericMorphism, firstArr, firstTys, List.ofFn_succ, Fren.Seq.nth_of_lt]

/-- An application of a generic function within itself, at its own type
parameters, applies the same instance: a generic structural recursion
recurses at its instance (`Reqs/Lang/Recursion#generic-recursion`). -/
theorem instantiatedArgs_own (outer : Array Fren.Core.Ty) (ns : Array Lean.Name) (h : ns.size = outer.size) :
    Fren.Core.instantiatedArgs outer (ns.mapIdx fun k n => Fren.Core.Ty.param k n) = outer := by
  apply Array.ext
  · simp [Fren.Core.instantiatedArgs, h]
  · intro i h1 h2
    simp [Fren.Core.instantiatedArgs, Fren.Core.genericMorphism, Fren.Core.Ty.subst]
    simp_all

-- For every generic function and whether it has a function parameter: the
-- check that both front ends make before a body may apply its own function
-- (`Core.selfApplicable`).
impl self_application: lang::self_application for (g h : Bool) {
  generic? := g,
  higher_order? := h,
  may_recurse? := Fren.Core.selfApplicable g h,
} by
  intro g h _
  cases g <;> cases h <;> simp [fren_spec, Fren.Core.selfApplicable]

/-- A check's verdict, as `lang::generic_contract` has it. -/
def decidedOf : Fren.Core.Verdict → lang.Decided
  | .pass => .Holds
  | .fail => .Fails
  | .inconclusive => .Undecided

-- For every verdict of the check of a generic function's contract at its
-- type parameters' sorts, and of its checks at the instances that the spec
-- applies: the checks that both front ends report (`Core.genericContract`).
impl generic_contract: lang::generic_contract for (o : Fren.Core.Verdict) (vs : List Fren.Core.Verdict) {
  at_sorts := decidedOf o,
  instances := Fren.Seq.ofList (vs.map decidedOf),
  reported := Fren.Seq.ofList ((Fren.Core.genericContract id o vs.toArray).toList.map decidedOf),
} by
  intro o vs _
  cases o <;> cases vs <;> simp [fren_spec, Fren.Core.genericContract, decidedOf, Fren.Seq.ext_iff]

/-- An item as `lang::instance_site` has it, from a file and the name that
`Core.siteOf` is given: the position, as a numeric name. -/
def itemName (i : Nat) : Lean.Name := .num .anonymous i

/-- A site as `lang::instance_site` has it. -/
def siteOf' : Option Fren.Core.InstanceSite → lang.CheckSite
  | none => .Unchecked
  | some .function => .AtFunction
  | some (.item f (.num _ i)) => .AtItem { file := f, item := i }
  | some (.item f _) => .AtItem { file := f, item := 0 }

-- For every file of a function, whether a run checks the function and
-- whether an earlier run checked the instance, and every list of the items
-- that the run checks and whose checks use an instance of it, in order:
-- where both front ends check the instance's contract (`Core.siteOf`,
-- which `Core.instanceSites` gives the first of them).
impl instance_site: lang::instance_site for (ff : Nat) (fc d : Bool) (us : List (Nat × Nat)) {
  function_file := ff,
  function_checked? := fc,
  done? := d,
  users := Fren.Seq.ofList (us.map fun (f, i) => ({ file := f, item := i } : lang.ItemAt)),
  site := siteOf' (Fren.Core.siteOf ff fc d (us.head?.map fun (f, i) => (f, itemName i))),
} by
  intro ff fc d us _
  cases us with
  | nil => cases fc <;> cases d <;> simp [fren_spec, Fren.Core.siteOf, siteOf']
  | cons u rest =>
    obtain ⟨f, i⟩ := u
    have hl : ¬ ((rest.length : Int) + 1 < 1) := by omega
    by_cases h : f = ff
    · cases fc <;> cases d <;> simp [fren_spec, Fren.Core.siteOf, siteOf', itemName, h, Fren.Seq.nth_of_lt, hl]
    · have h' : ¬ ((f : Int) = ff) := by exact_mod_cast h
      cases fc <;> cases d <;> simp [fren_spec, Fren.Core.siteOf, siteOf', itemName, h, Fren.Seq.nth_of_lt, hl, h']

end Fren.Impls
