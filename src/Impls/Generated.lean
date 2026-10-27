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

/-! # The forms of generated definitions (`Reqs/Generated#matches`, `Reqs/Generated#computable-definitions`)

`Fren.matchForm`, which decides whether a `match` in a defined function's
Lean definition is Lean's, and `Fren.definitionForm`, which decides whether
a generated definition is compiled, over their inputs as the spec models
them. -/

def headOf : Fren.PatHead → generated.Head
  | .wildcard => .Wildcard | .binder => .Binder | .variant => .Variant | .literal => .Literal | .orPattern => .OrPattern

def scrutineeOf : Fren.ScrutineeKind → generated.Scrutinee
  | .enumeration => .Enumeration | .other => .Other

def armKindOf : Fren.ArmKind → generated.ArmKind
  | .values => .Values | .propositions => .Propositions

def matchFormOf : Fren.MatchForm → generated.MatchForm
  | .leanMatch => .LeanMatch | .ifChain => .IfChain

theorem headOf_eq_literal (h : Fren.PatHead) : headOf h = .Literal ↔ h = .literal := by
  cases h <;> simp [headOf]

theorem headOf_eq_orPattern (h : Fren.PatHead) : headOf h = .OrPattern ↔ h = .orPattern := by
  cases h <;> simp [headOf]

impl match_form: generated::match_form for (s : Fren.ScrutineeKind) (a : Fren.ArmKind) (hs : List Fren.PatHead) {
  scrutinee := scrutineeOf s,
  arms := armKindOf a,
  heads := Fren.FinSet.ofList (hs.map headOf),
  form := matchFormOf (Fren.matchForm s a hs.toArray),
} by
  intro s a hs _
  cases s <;> cases a <;>
    simp [fren_spec, Fren.matchForm, scrutineeOf, armKindOf, matchFormOf, headOf_eq_literal, headOf_eq_orPattern] <;>
    split <;> simp_all

def valueKindOf : Fren.ValueKind → generated.ValueKind
  | .proposition => .Proposition | .data => .Data

def mentionOf : Fren.Mention → generated.Mention
  | .computable => .Computable | .classicalDecision => .ClassicalDecision
  | .noncomputableDecl => .NoncomputableDecl | .dataAxiom => .DataAxiom

def definitionFormOf : Fren.DefinitionForm → generated.DefinitionForm
  | .notCompiled => .NotCompiled | .compiled => .Compiled | .markedNoncomputable => .MarkedNoncomputable

theorem mentionOf_eq_classicalDecision (m : Fren.Mention) : mentionOf m = .ClassicalDecision ↔ m = .classicalDecision := by
  cases m <;> simp [mentionOf]

theorem mentionOf_eq_noncomputableDecl (m : Fren.Mention) : mentionOf m = .NoncomputableDecl ↔ m = .noncomputableDecl := by
  cases m <;> simp [mentionOf]

theorem mentionOf_eq_dataAxiom (m : Fren.Mention) : mentionOf m = .DataAxiom ↔ m = .dataAxiom := by
  cases m <;> simp [mentionOf]

impl definition_form: generated::definition_form for (v : Fren.ValueKind) (ms : List Fren.Mention) {
  value := valueKindOf v,
  mentions := Fren.FinSet.ofList (ms.map mentionOf),
  form := definitionFormOf (Fren.definitionForm v ms.toArray),
} by
  intro v ms _
  cases v <;>
    simp [fren_spec, Fren.definitionForm, valueKindOf, definitionFormOf, mentionOf_eq_classicalDecision,
      mentionOf_eq_noncomputableDecl, mentionOf_eq_dataAxiom] <;>
    by_cases h : (Fren.Mention.classicalDecision ∈ ms ∨ Fren.Mention.noncomputableDecl ∈ ms) ∨ Fren.Mention.dataAxiom ∈ ms <;>
    simp_all [definitionFormOf]

end Fren.Impls.Generated

