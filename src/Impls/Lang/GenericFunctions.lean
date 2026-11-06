-- keep-sorted start
import Impls.Check
import Impls.Lang.Construction
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-! ## Generic functions (`Reqs/Lang/GenericFunctions`) -/

-- For every number of type parameters, and whether one of them is not in
-- the signature: the check that both front ends make of a function's
-- declaration, defined or not (`Core.genericFunctionAccepted`).
impl generic_function: lang::generic_function for (params : Nat) (u : Bool) {
  params := params,
  unmentioned? := u,
  accepted? := Fren.Core.genericFunctionAccepted params u,
} by
  intro params u _
  cases u <;> simp [fren_spec, Fren.Core.genericFunctionAccepted]

/-- Whose type parameter an element type is (`lang::ParamOwner`). -/
def toParamOwner : Fren.Core.ParamOwner → lang.ParamOwner
  | .datatype => .Datatype
  | .function => .Function

-- For a generic type's type parameter, including nested collection
-- payloads and fields, and a generic function's, with the shared check
-- (`Core.elementParamAccepted`).
impl element_parameter: lang::element_parameter for (o : Fren.Core.ParamOwner) {
  owner := toParamOwner o,
  accepted? := Fren.Core.elementParamAccepted o,
} by
  intro o _
  cases o <;> simp [fren_spec, Fren.Core.elementParamAccepted, Fren.Core.typeParamPlaceAccepted]

interp lang::ty_mentions? := fun (t : Fren.Core.Ty) (k : Nat) => t.mentions k

/-- The parameters' declared types `ts`, the first `d` of them. -/
def firstTys (d : Fin 4) (ts : Fin 3 → Fren.Core.Ty) : List Fren.Core.Ty := (List.ofFn ts).take d

/-- Whether the type parameter `k` is mentioned by the signature
(`Core.inSignature`), over the first three parameters at most. -/
theorem inSignature_eq (d : Fin 4) (ts : Fin 3 → Fren.Core.Ty) (r : Fren.Core.Ty) (k : Nat) :
    Fren.Core.inSignature (firstTys d ts).toArray r k =
      (r.mentions k || (decide (0 < (d : Nat)) && (ts 0).mentions k) || (decide (1 < (d : Nat)) && (ts 1).mentions k)
        || (decide (2 < (d : Nat)) && (ts 2).mentions k)) := by
  obtain ⟨_ | _ | _ | _ | d, hd⟩ := d <;> first | omega |
    simp [Fren.Core.inSignature, firstTys, List.ofFn_succ, Bool.or_assoc]

/-- Whether one of the first `n` type parameters, three at most, is not in
the signature (`Core.firstUnmentioned?`). -/
theorem unmentioned_eq (decl : Array Fren.Core.Ty) (r : Fren.Core.Ty) (n : Fin 4) :
    (Fren.Core.firstUnmentioned? decl r n).isSome =
      ((decide (0 < (n : Nat)) && !Fren.Core.inSignature decl r 0) || (decide (1 < (n : Nat)) && !Fren.Core.inSignature decl r 1)
        || (decide (2 < (n : Nat)) && !Fren.Core.inSignature decl r 2)) := by
  obtain ⟨_ | _ | _ | _ | n, hn⟩ := n <;> first | omega | skip
  all_goals
    cases h0 : Fren.Core.inSignature decl r 0 <;> cases h1 : Fren.Core.inSignature decl r 1 <;>
      cases h2 : Fren.Core.inSignature decl r 2 <;> simp [Fren.Core.firstUnmentioned?, List.range_succ, h0, h1, h2]

-- For every function with at most three parameters and three type
-- parameters, and every signature: the check that both front ends make of
-- its declaration (`Core.genericFunctionAccepted`, `Core.firstUnmentioned?`).
impl generic_signature: lang::generic_signature
    for (n : Fin 4) (d : Fin 4) (ts : Fin 3 → Fren.Core.Ty) (r : Fren.Core.Ty) {
  params := (n : Nat),
  declared := Fren.Seq.ofList (firstTys d ts),
  result := r,
  in0? := Fren.Core.inSignature (firstTys d ts).toArray r 0,
  in1? := Fren.Core.inSignature (firstTys d ts).toArray r 1,
  in2? := Fren.Core.inSignature (firstTys d ts).toArray r 2,
  unmentioned? := (Fren.Core.firstUnmentioned? (firstTys d ts).toArray r n).isSome,
  accepted? := Fren.Core.genericFunctionAccepted n (Fren.Core.firstUnmentioned? (firstTys d ts).toArray r n).isSome,
} by
  intro n d ts r _
  simp only [unmentioned_eq, inSignature_eq]
  obtain ⟨_ | _ | _ | _ | d, hd⟩ := d <;> first | omega | skip
  all_goals obtain ⟨_ | _ | _ | _ | n, hn⟩ := n <;> first | omega | skip
  all_goals
    simp [fren_spec, firstTys, List.ofFn_succ, Fren.Core.genericFunctionAccepted, Fren.Seq.nth_of_lt, Bool.or_assoc] <;>
    grind

/-- What matching the type expected of an application against the declared
result type gives the type parameter `k`, before it is widened. -/
def resultMatch (result : Fren.Core.Ty) (expected? : Option Fren.Core.Ty) (k : Nat) : Option Fren.Core.Ty :=
  expected?.bind (Fren.Core.matchParam k result ·)

theorem expectedArgs_at (result : Fren.Core.Ty) (expected? : Option Fren.Core.Ty) (k : Nat) :
    (Fren.Core.expectedArgs result expected? (k + 1))[k]?.join = (resultMatch result expected? k).map (·.widen) := by
  cases expected? <;> simp [Fren.Core.expectedArgs, resultMatch]

-- For every type parameter `k` of a generic function, the declared types of
-- its parameters and the types of the arguments that synthesize them, its
-- declared result type and the type expected of an application, if one
-- is: the inference that both front ends make (`Core.inferCallArg`, which
-- `Core.inferCall` applies to each type parameter, first with no argument
-- elaborated, then once the first that gives it an argument is). With no argument, the one that the
-- definition gives stands in for it.
impl call_type_argument: lang::call_type_argument
    for (declared : Array Fren.Core.Ty) (found : Array (Option Fren.Core.Ty)) (result : Fren.Core.Ty)
      (expected? : Option Fren.Core.Ty) (k : Nat) {
  declared := Fren.Seq.ofList declared.toList,
  synthesizes := Fren.Seq.ofList (found.map Option.isSome).toList,
  k := k,
  result_matched? := (resultMatch result expected? k).isSome,
  result_arg := (resultMatch result expected? k).getD .bool,
  matched? := (giverMatch declared found k).isSome,
  matched := (giverMatch declared found k).getD .bool,
  giver := Fren.Core.firstGiver declared (found.map Option.isSome) k,
  known? := (Fren.Core.inferCallArg declared found result expected? k).isSome,
  argument := (Fren.Core.inferCallArg declared found result expected? k).getD .bool,
} by
  intro declared found result expected? k _
  have hs : (found.toList.map Option.isSome).toArray = found.map Option.isSome := by cases found; simp
  simp only [Fren.Core.inferCallArg, expectedArgs_at]
  cases hr : resultMatch result expected? k with
  | some a => simp [fren_spec, hs]
  | none =>
    simp [fren_spec, Fren.Core.inferArg, giverMatch, hs]
    generalize Fren.Core.firstGiver declared (found.map Option.isSome) k = j
    by_cases hj : j < 0
    · simp [hj, Fren.Core.Ty.widen]
    · have h0 : 0 ≤ j := by omega
      cases found[j.toNat]?.join with
      | none => simp [h0, Fren.Core.Ty.widen]
      | some f =>
        cases hm : Fren.Core.matchParam k declared[j.toNat]! f <;> simp [hj, h0, hm, Fren.Core.Ty.widen]

/-- `Core.inferCall` on an application of a generic function with `n` type
parameters, `T0`, `T1`, ..., whose arguments are `vs`, where the expected
type gives an argument to each type parameter that `fr` says: its result
type is an instance of `R` with those parameters, and the expected type
the instance with `Bool` for each. Gives its type arguments, the positions
of the arguments in the order in which it elaborates them, and whether it
reports the arguments unknown, as `runConstruction` does. -/
def runCall (n : Nat) (vs : List lang.ArgMode) (fr : List Bool) : Array Fren.Core.Ty × (List Nat × Bool) :=
  let given := (List.range n).filter (fr.getD · false)
  (Fren.Core.inferCall (m := StateM (List Nat × Bool)) (Array.replicate n .anonymous) (vs.map valueTy).toArray
    (.enum .anonymous (given.map fun i => .param i .anonymous)) (vs.map valueSynthesizes).toArray
    (some (.enum .anonymous (given.map fun _ => .bool)))
    (modify fun s => (s.1, true))
    (fun k _ => do modify (fun s => (s.1 ++ [k], s.2)); pure (some .int))
    (fun _ _ _ => pure ())).run ([], false)

/-- Every list of `n` `Bool`s. -/
def boolLists : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (boolLists n).flatMap fun l => [false :: l, true :: l]

theorem mem_boolLists : (l : List Bool) → l ∈ boolLists l.length
  | [] => by simp [boolLists]
  | b :: l => by
    simp only [boolLists, List.length_cons, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false]
    exact ⟨l, mem_boolLists l, by cases b <;> simp⟩

/-- The obligation of `call_order` for `n`, `vs` and `fr`. -/
abbrev callObligation (n : Nat) (vs : List lang.ArgMode) (fr : List Bool) : Prop :=
  lang.call_order.assumes n (Seq.ofList vs) (Seq.ofList fr)
    (Seq.ofList ((runCall n vs fr).2.1.map Int.ofNat))
    (Seq.ofList ((runCall n vs fr).1.toList.map fun t => !isParam t))
    (runCall n vs fr).2.2 →
  lang.call_order.defs n (Seq.ofList vs) (Seq.ofList fr)
      (Seq.ofList ((runCall n vs fr).2.1.map Int.ofNat))
      (Seq.ofList ((runCall n vs fr).1.toList.map fun t => !isParam t))
      (runCall n vs fr).2.2 ∧
    lang.call_order.ensures n (Seq.ofList vs) (Seq.ofList fr)
      (Seq.ofList ((runCall n vs fr).2.1.map Int.ofNat))
      (Seq.ofList ((runCall n vs fr).1.toList.map fun t => !isParam t))
      (runCall n vs fr).2.2

/-- The obligation for every application of at most two arguments, of a
function with `n` type parameters to which the expected type gives
arguments as `fr` says, by evaluation. -/
noncomputable def callCases (n : Nat) (fr : List Bool) : Bool := (argModeLists 2).all fun vs => decide (callObligation n vs fr)

-- One theorem for each `n` and `fr`, each checked by the kernel apart.
theorem call_order_cases_0 : callCases 0 [] = true := by decide +kernel
theorem call_order_cases_1_f : callCases 1 [false] = true := by decide +kernel
theorem call_order_cases_1_t : callCases 1 [true] = true := by decide +kernel
theorem call_order_cases_2_f_f : callCases 2 [false, false] = true := by decide +kernel
theorem call_order_cases_2_f_t : callCases 2 [false, true] = true := by decide +kernel
theorem call_order_cases_2_t_f : callCases 2 [true, false] = true := by decide +kernel
theorem call_order_cases_2_t_t : callCases 2 [true, true] = true := by decide +kernel
theorem call_order_cases_3_f_f_f : callCases 3 [false, false, false] = true := by decide +kernel
theorem call_order_cases_3_f_f_t : callCases 3 [false, false, true] = true := by decide +kernel
theorem call_order_cases_3_f_t_f : callCases 3 [false, true, false] = true := by decide +kernel
theorem call_order_cases_3_f_t_t : callCases 3 [false, true, true] = true := by decide +kernel
theorem call_order_cases_3_t_f_f : callCases 3 [true, false, false] = true := by decide +kernel
theorem call_order_cases_3_t_f_t : callCases 3 [true, false, true] = true := by decide +kernel
theorem call_order_cases_3_t_t_f : callCases 3 [true, true, false] = true := by decide +kernel
theorem call_order_cases_3_t_t_t : callCases 3 [true, true, true] = true := by decide +kernel

/-- The obligation for every application of at most two arguments, of a
function with at most three type parameters. -/
theorem call_order_cases : ((List.range 4).all fun n => (boolLists n).all (callCases n)) = true := by
  simp [List.range_succ, boolLists, call_order_cases_0, call_order_cases_1_f, call_order_cases_1_t, call_order_cases_2_f_f, call_order_cases_2_f_t, call_order_cases_2_t_f, call_order_cases_2_t_t, call_order_cases_3_f_f_f, call_order_cases_3_f_f_t, call_order_cases_3_f_t_f, call_order_cases_3_f_t_t, call_order_cases_3_t_f_f, call_order_cases_3_t_f_t, call_order_cases_3_t_t_f, call_order_cases_3_t_t_t]

-- For every application of at most two arguments, of a generic function
-- with at most three type parameters, and every set of type parameters
-- that the expected type gives an argument: the order in which both front
-- ends elaborate its arguments, and the arguments that they infer
-- (`Core.inferCall`), run with the elaboration of each argument recorded.
impl call_order: lang::call_order for (n : Fin 4) (vs : List lang.ArgMode) (fr : List Bool) {
  params := (n : Nat),
  values := Fren.Seq.ofList vs,
  from_result := Fren.Seq.ofList fr,
  order := Fren.Seq.ofList ((runCall n vs fr).2.1.map Int.ofNat),
  given := Fren.Seq.ofList ((runCall n vs fr).1.toList.map fun t => !isParam t),
  unknown? := (runCall n vs fr).2.2,
} by
  intro n vs fr h
  have h' := h
  simp only [fren_spec] at h'
  have h3 := h'.1
  simp at h3
  have hl : vs.length ≤ 2 := by omega
  have hf : fr.length = (n : Nat) := by omega
  have := call_order_cases
  simp only [List.all_eq_true, callCases, decide_eq_true_eq] at this
  exact this n (by simp) fr (by rw [← hf]; exact mem_boolLists fr) vs (mem_argModeLists 2 vs hl) h

end Fren.Impls
