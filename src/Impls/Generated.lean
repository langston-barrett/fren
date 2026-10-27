-- keep-sorted start
import Fren.Impl
import Reqs.Generated
-- keep-sorted end
open Fren.Lang

/-! # The names of generated declarations (`Reqs/Generated#names`)

`Fren.leanName`, the one function that names every declaration the hosted
front end generates, over names given by their components. -/

namespace Fren.Impls.Generated

/-- The name whose components are `l`, in order. -/
def ofSegs (l : List String) : Lean.Name := l.foldl .str .anonymous

/-- The components of `n`, in order: a number's as its digits. -/
def segsOf : Lean.Name → List String
  | .anonymous => []
  | .str p s => segsOf p ++ [s]
  | .num p k => segsOf p ++ [toString k]

theorem segsOf_foldl (n : Lean.Name) (l : List String) : segsOf (l.foldl .str n) = segsOf n ++ l := by
  induction l generalizing n with
  | nil => simp
  | cons x l ih => simp [List.foldl, ih, segsOf]

theorem underName_foldl (pre n : Lean.Name) (l : List String) :
    underName pre (l.foldl .str n) = l.foldl .str (underName pre n) := by
  induction l generalizing n with
  | nil => rfl
  | cons x l ih => simp only [List.foldl, ih]; rfl

theorem segsOf_leanName (c p : List String) :
    segsOf (leanName (ofSegs c) (ofSegs p)) = c ++ ["Fren", "Generated"] ++ p := by
  simp only [leanName, ofSegs, underName_foldl]
  rw [segsOf_foldl]
  have : underName (underName (List.foldl .str .anonymous c) generatedNamespace) .anonymous =
      .str (.str (List.foldl .str .anonymous c) "Fren") "Generated" := rfl
  rw [this]
  simp [segsOf, segsOf_foldl]

-- The real naming function, over every namespace and path.
impl lean_name: generated::lean_name for (c p : List String) {
  current := Fren.Seq.ofList c,
  path := Fren.Seq.ofList p,
  name := Fren.Seq.ofList (segsOf (leanName (ofSegs c) (ofSegs p))),
} by
  intro c p _
  simp [fren_spec, segsOf_leanName, Fren.Seq.ext_iff]

/-! # The prelude's types (`Reqs/Generated#the-preludes-types`)

The Lean types that both front ends give the prelude's types, as
`Fren.Core.leanTypeOf?` finds them by their paths. -/

/-- The Lean type of the prelude type `t`, as the front ends find it. -/
def leanOf (t : generated.PreludeType) : Fren.Core.LeanType :=
  (Fren.Core.leanTypeOf? (Fren.Core.preludeModule ++ match t with | .Option => `Option | .Result => `Result)).getD default

impl prelude_type: generated::prelude_type for (t : generated.PreludeType) (args : List String) {
  ty := t,
  args := Fren.Seq.ofList args,
  lean := (leanOf t).lean.getString!,
  lean_args := Fren.Seq.ofList ((leanOf t).leanArgs args.toArray).toList,
} by
  intro t args _
  have ho : leanOf .Option = Fren.Core.leanTypes[0]! := rfl
  have hr : leanOf .Result = Fren.Core.leanTypes[1]! := rfl
  cases t <;> rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, args⟩⟩⟩ <;>
    simp [fren_spec, ho, hr, Fren.Core.leanTypes, Fren.Core.LeanType.leanArgs, Fren.Seq.ext_iff] <;>
    first | rfl | exact ⟨rfl, by omega⟩

/-- The prelude type of the variant `v`, and the variant's position among
its type's variants, as `Prelude.fren` declares them, which is the position
that both front ends give the variant. -/
def preludeVariantOf (v : generated.PreludeVariant) : Fren.Core.LeanType × Nat :=
  match v with
  | .None => (leanOf .Option, 0) | .Some => (leanOf .Option, 1) | .Ok => (leanOf .Result, 0) | .Err => (leanOf .Result, 1)

def preludeTypeOfVariant : generated.PreludeVariant → generated.PreludeType
  | .None | .Some => .Option
  | .Ok | .Err => .Result

/-- A name's components joined by `.`, as `Lean.Name.toString` joins a name
without characters to escape, by a recursion that `decide` reduces. -/
def dotted : Lean.Name → String
  | .str .anonymous s => s
  | .str p s => dotted p ++ "." ++ s
  | _ => ""

impl prelude_variant: generated::prelude_variant for (v : generated.PreludeVariant) {
  variant := v,
  ty := preludeTypeOfVariant v,
  ctor := dotted ((preludeVariantOf v).1.ctors[(preludeVariantOf v).2]!),
  selectors := Fren.Seq.ofList ((preludeVariantOf v).1.selectors[(preludeVariantOf v).2]!).toList,
  position := (((preludeVariantOf v).1.ctorOrder.idxOf? (preludeVariantOf v).2).getD 0 : Nat),
} by
  intro v _
  have ho : leanOf .Option = Fren.Core.leanTypes[0]! := rfl
  have hr : leanOf .Result = Fren.Core.leanTypes[1]! := rfl
  cases v <;> simp [fren_spec, ho, hr, preludeVariantOf, preludeTypeOfVariant, dotted, Fren.Core.leanTypes, Fren.Seq.ext_iff] <;>
    first | rfl | decide

end Fren.Impls.Generated

