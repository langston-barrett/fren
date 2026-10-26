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

end Fren.Impls.Generated
