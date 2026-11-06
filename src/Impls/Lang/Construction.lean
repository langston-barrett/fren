-- keep-sorted start
import Impls.Check
import Impls.Lang.Generics
import Impls.Lang.TypeParameters
import Impls.Lang.Typing
import Reqs.Lang
-- keep-sorted end
open Fren.Lang

namespace Fren.Impls

/-- The type parameters `T0`, `T1`, ... of a generic type with `n` of them. -/
def typeParamNames (n : Nat) : Array Lean.Name := ((List.range n).map fun i => Lean.Name.mkSimple s!"T{i}").toArray

theorem anySynthesizes_given (vs : List lang.ArgMode) (k : Nat) (hk : k < 3) :
    Fren.Core.TypeShape.anySynthesizes (List.map (fun x => x.snd)
      (List.filter (fun x => Fren.Core.Ty.mentions k x.fst) ((vs.map valueTy).zip (vs.map valueShape))))
      = decide (lang.ArgMode.Gives (argOf k) ∈ vs) := by
  rw [anySynthesizes_eq_any]
  induction vs with
  | nil => simp
  | cons v vs ih =>
    rcases v with a | a <;> cases a <;>
      (obtain _ | _ | _ | k := k <;>
        simp_all [valueTy, valueShape, argTy, argOf, Fren.Core.Ty.mentions, Fren.Core.TypeShape.synthesizes]) <;>
      omega

-- For every generic type with at most three type parameters and every
-- construction's values: the shape that both front ends decide by
-- (`Core.constructionShape`, by way of `Core.inferConstruction`), and
-- whether it synthesizes its type.
impl construction_synthesis: lang::construction_synthesis for (n : Fin 4) (vs : List lang.ArgMode) {
  params := (n : Nat),
  values := Fren.Seq.ofList vs,
  synthesizes? := (Fren.Core.constructionShape (typeParamNames n) (vs.map valueTy).toArray
    (vs.map valueShape).toArray).synthesizes,
} by
  intro n vs _
  simp only [fren_spec]
  simp only [Fren.Core.constructionShape, Fren.Core.TypeShape.synthesizes, allGiven_eq_all]
  obtain ⟨n, hn⟩ := n
  obtain _ | _ | _ | _ | n := n
  all_goals first | omega | skip
  all_goals simp [typeParamNames, List.range_succ, Fren.Core.TypeShape.synthesizes, anySynthesizes_given _ 0 (by omega),
    anySynthesizes_given _ 1 (by omega), anySynthesizes_given _ 2 (by omega), argOf, and_assoc]
/-- What matching the type of the first of a construction's values that
synthesizes its type, and whose declared type mentions the type parameter
`k`, against its declared type gives `k`, before it is widened
(`Core.inferArg`). -/
def giverMatch (declared : Array Fren.Core.Ty) (found : Array (Option Fren.Core.Ty)) (k : Nat) :
    Option Fren.Core.Ty :=
  let j := Fren.Core.firstGiver declared (found.map Option.isSome) k
  if j < 0 then none else do Fren.Core.matchParam k declared[j.toNat]! (← found[j.toNat]?.join)

-- For every type parameter `k` of a generic type with `n` of them, the
-- declared types of a construction's values and the types of those that
-- synthesize them, and the arguments of the instance expected of it, if one
-- is: the inference that both front ends make (`Core.inferArg`, by way of
-- `Core.inferConstruction`). With no argument, the one that the definition
-- gives stands in for it.
impl type_argument_inference: lang::type_argument_inference
    for (n : Nat) (k : Fin n) (declared : Array Fren.Core.Ty) (found : Array (Option Fren.Core.Ty))
      (expected? : Option (Vector Fren.Core.Ty n)) {
  declared := Fren.Seq.ofList declared.toList,
  synthesizes := Fren.Seq.ofList (found.map Option.isSome).toList,
  k := k,
  expected? := expected?.isSome,
  expected_arg := (expected?.map (·[k])).getD .bool,
  matched? := (giverMatch declared found k).isSome,
  matched := (giverMatch declared found k).getD .bool,
  giver := Fren.Core.firstGiver declared (found.map Option.isSome) k,
  known? := (Fren.Core.inferArg declared found (expected?.map (·.toArray)) k).isSome,
  argument := (Fren.Core.inferArg declared found (expected?.map (·.toArray)) k).getD .bool,
} by
  intro n k declared found expected? _
  have hs : (found.toList.map Option.isSome).toArray = found.map Option.isSome := by cases found; simp
  cases expected? with
  | some as => simp [fren_spec, Fren.Core.inferArg, hs]
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

/-- Whether a construction's value synthesizes its type (`lang::ArgMode`). -/
def valueSynthesizes : lang.ArgMode → Bool
  | .Gives _ => true
  | .Waits _ => false

/-- `Core.inferConstruction` on a construction of a generic type with `n` type
parameters, `T0`, `T1`, ..., whose values are `vs`, with an instance
expected of it if `expected` is: its type arguments, the positions of the
values in the order in which it elaborates them, and whether it reports the
arguments unknown. Each value elaborated has the type `Int`, and an expected
instance has the arguments `Bool`, so that the parameters with arguments are
those that are not type parameters in the result. -/
def runConstruction (n : Nat) (vs : List lang.ArgMode) (expected : Bool) : Array Fren.Core.Ty × (List Nat × Bool) :=
  (Fren.Core.inferConstruction (m := StateM (List Nat × Bool)) (Array.replicate n .anonymous) (vs.map valueTy).toArray
    (vs.map valueSynthesizes).toArray (if expected then some (Array.replicate n .bool) else none)
    (modify fun s => (s.1, true))
    (fun k _ => do modify (fun s => (s.1 ++ [k], s.2)); pure (some .int))
    (fun _ _ _ => pure ())).run ([], false)

/-- Every `lang::ArgMode`. -/
def allArgModes : List lang.ArgMode :=
  [.Gives .P0, .Gives .P1, .Gives .P2, .Gives .Other, .Waits .P0, .Waits .P1, .Waits .P2, .Waits .Other]

/-- Every list of at most `k` values. -/
def argModeLists : Nat → List (List lang.ArgMode)
  | 0 => [[]]
  | k + 1 => [] :: (allArgModes.flatMap fun v => (argModeLists k).map (v :: ·))

/-- The obligation of `construction_order` for `n`, `vs` and `e`. -/
abbrev orderObligation (n : Nat) (vs : List lang.ArgMode) (e : Bool) : Prop :=
  lang.construction_order.assumes n (Seq.ofList vs) e
    (Seq.ofList ((runConstruction n vs e).2.1.map Int.ofNat))
    (Seq.ofList ((runConstruction n vs e).1.toList.map fun t => !isParam t))
    (runConstruction n vs e).2.2 →
  lang.construction_order.defs n (Seq.ofList vs) e
      (Seq.ofList ((runConstruction n vs e).2.1.map Int.ofNat))
      (Seq.ofList ((runConstruction n vs e).1.toList.map fun t => !isParam t))
      (runConstruction n vs e).2.2 ∧
    lang.construction_order.ensures n (Seq.ofList vs) e
      (Seq.ofList ((runConstruction n vs e).2.1.map Int.ofNat))
      (Seq.ofList ((runConstruction n vs e).1.toList.map fun t => !isParam t))
      (runConstruction n vs e).2.2

theorem mem_argModeLists : (k : Nat) → (vs : List lang.ArgMode) → vs.length ≤ k → vs ∈ argModeLists k
  | 0, [], _ => by simp [argModeLists]
  | k + 1, [], _ => by simp [argModeLists]
  | k + 1, v :: vs, h => by
    simp only [argModeLists, List.mem_cons, List.mem_flatMap, List.mem_map]
    refine .inr ⟨v, ?_, vs, mem_argModeLists k vs (by simp at h; omega), rfl⟩
    rcases v with (_ | _ | _ | _) | (_ | _ | _ | _) <;> decide

/-- The obligation for every construction of at most three values, of a type
with at most three type parameters, by evaluation. -/
theorem construction_order_cases : ((List.range 4).all fun n => [false, true].all fun e => (argModeLists 3).all fun vs =>
    decide (orderObligation n vs e)) = true := by decide +kernel

-- For every construction of at most three values, of a generic type with at
-- most three type parameters, and with an instance expected of it or not:
-- the order in which both front ends elaborate its values, and the
-- arguments that they infer (`Core.inferConstruction`), run with the
-- elaboration of each value recorded.
impl construction_order: lang::construction_order for (n : Fin 4) (vs : List lang.ArgMode) (e : Bool) {
  params := (n : Nat),
  values := Fren.Seq.ofList vs,
  expected? := e,
  order := Fren.Seq.ofList ((runConstruction n vs e).2.1.map Int.ofNat),
  given := Fren.Seq.ofList ((runConstruction n vs e).1.toList.map fun t => !isParam t),
  unknown? := (runConstruction n vs e).2.2,
} by
  intro n vs e h
  have hl : vs.length ≤ 3 := by
    have h' := h
    simp only [fren_spec] at h'
    have h3 := h'.1.1
    simp at h3
    omega
  have := construction_order_cases
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  exact this n (by simp) e (by cases e <;> simp) vs (mem_argModeLists 3 vs hl) h

end Fren.Impls
