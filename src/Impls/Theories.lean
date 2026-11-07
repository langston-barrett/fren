-- keep-sorted start
import FrenCore.Theories
import Impls.Lang.Instances
import Impls.Lang.Types
import Reqs.Lang
-- keep-sorted end

open Fren.Lang

/-! The equations expose each node and tail of the core's inputs. The
interpretations below are constructors, projections and the recursive
operations whose defining equations the `impl`s prove, for every input. -/

namespace Fren.Impls.Theories

open Fren.Core
open Lean (Name)

interp lang::TheoryName := Name
interp lang::TheoryDeclaration := TheoryDeclaration
interp lang::TheoryEntries := List TheoryEntry
interp lang::TheoryDeclarations := List TheoryDeclaration
interp lang::TheoryTerm := TheoryTerm
interp lang::TheoryTerms := List TheoryTerm
interp lang::TheoryVariables := List (Name × Ty)
interp lang::TheorySentence := TheorySentence
interp lang::TheoryMorphism := TheoryMorphism
interp lang::TheorySubstitution := Name → Option TheoryTerm

interp lang::theory_entries_empty? := fun (es : List TheoryEntry) => es.isEmpty
interp lang::theory_entry_kind := fun (es : List TheoryEntry) =>
  match es with | .declaration _ :: _ => lang.TheoryEntryKind.Declaration | _ => .Sentence
interp lang::theory_entry_declaration := fun (es : List TheoryEntry) =>
  match es with | .declaration d :: _ => d | _ => default
interp lang::theory_entries_rest := fun (es : List TheoryEntry) => es.tail
interp lang::theory_no_declarations := fun (_ : List TheoryEntry) => ([] : List TheoryDeclaration)
interp lang::theory_add_declaration := fun (d : TheoryDeclaration) ds => d :: ds
interp lang::signature_items := theorySignatureItems

impl theory_signature: lang::theory_signature for (t : Theory) {
  parameters := t.parameters,
  entries := t.entries,
  signature_parameters := t.signature.parameters,
  items := t.signature.items,
} by
  intro t _
  rcases t with ⟨ps, es⟩
  cases es with
  | nil => simp [fren_spec, Theory.signature, theorySignatureItems]
  | cons e es => cases e <;> simp [fren_spec, Theory.signature, theorySignatureItems]

def termKind : TheoryTerm → lang.TheoryTermKind
  | .variable _ => .Variable
  | .bound _ => .Bound
  | .query _ => .Query
  | .item _ => .Item
  | .literal _ => .Literal
  | .sort _ => .TypeArg
  | .app .. => .Apply
  | .all .. => .All
  | .ex .. => .Exists

interp lang::theory_term_kind := termKind
interp lang::theory_term_name := fun (t : TheoryTerm) =>
  match t with | .variable n | .query n | .item n => n | _ => .anonymous
interp lang::theory_term_index := fun (t : TheoryTerm) => match t with | .bound k => k | _ => 0
interp lang::theory_term_type := fun (t : TheoryTerm) =>
  match t with | .sort ty | .all ty _ | .ex ty _ => ty | _ => default
interp lang::theory_term_left := fun (t : TheoryTerm) =>
  match t with | .app f _ | .all _ f | .ex _ f => f | _ => default
interp lang::theory_term_right := fun (t : TheoryTerm) => match t with | .app _ a => a | _ => default
interp lang::theory_item := TheoryTerm.item
interp lang::theory_type_arg := TheoryTerm.sort
interp lang::theory_apply := TheoryTerm.app
interp lang::theory_all := TheoryTerm.all
interp lang::theory_exists := TheoryTerm.ex
interp lang::theory_type_image := fun (m : TheoryMorphism) t => m.type t
interp lang::theory_item_image := fun (m : TheoryMorphism) n => m.item n
interp lang::translate_term := fun (m : TheoryMorphism) t => t.translate m

impl theory_term_translation: lang::theory_term_translation for (m : TheoryMorphism) (t : TheoryTerm) {
  m := m,
  term := t,
  translated := t.translate m,
} by
  intro m t _
  cases t <;> simp [fren_spec, termKind, TheoryTerm.translate]

interp lang::ground_term? := fun (t : TheoryTerm) depth => t.ground depth

impl theory_ground_term: lang::theory_ground_term for (t : TheoryTerm) (depth : Nat) {
  term := t,
  depth := depth,
  ground? := t.ground depth,
} by
  intro t depth _
  cases t <;> simp [fren_spec, termKind, TheoryTerm.ground]

interp lang::theory_variable_names := fun (vs : List (Name × Ty)) => Fren.FinSet.ofList (vs.map (·.1))
interp lang::theory_image_present? := fun (s : Name → Option TheoryTerm) n => (s n).isSome
interp lang::theory_image_term := fun (s : Name → Option TheoryTerm) n => (s n).getD default
interp lang::substitute_term := fun (s : Name → Option TheoryTerm) (vs : List (Name × Ty)) t =>
  t.substitute (theorySubstitution vs s)

impl theory_term_substitution: lang::theory_term_substitution for (s : Name → Option TheoryTerm)
    (vs : List (Name × Ty)) (t : TheoryTerm) {
  s := s,
  variables := vs,
  term := t,
  substituted := t.substitute (theorySubstitution vs s),
} by
  intro s vs t _
  cases t with
  | «variable» n =>
    have mem : n ∈ Fren.FinSet.ofList (vs.map Prod.fst) ↔ vs.any (·.1 == n) = true := by
      simp only [Fren.FinSet.mem_ofList, List.mem_map, List.any_eq_true, beq_iff_eq]
    cases h : vs.any (·.1 == n) <;> cases hn : s n <;>
      simp [fren_spec, termKind, TheoryTerm.substitute, theorySubstitution, mem, h, hn]
  | _ => simp [fren_spec, termKind, TheoryTerm.substitute]

interp lang::theory_variables_empty? := fun (vs : List (Name × Ty)) => vs.isEmpty
interp lang::theory_variable_name := fun (vs : List (Name × Ty)) => (vs.headD default).1
interp lang::theory_variable_type := fun (vs : List (Name × Ty)) => (vs.headD default).2
interp lang::theory_variables_rest := fun (vs : List (Name × Ty)) => vs.tail
interp lang::theory_no_variables := fun (_ : List (Name × Ty)) => ([] : List (Name × Ty))
interp lang::theory_add_variable := fun (n : Name) (t : Ty) vs => (n, t) :: vs
interp lang::remaining_variables := fun (s : Name → Option TheoryTerm) vs => theoryRemainingVariables vs s
interp lang::ground_images? := fun (s : Name → Option TheoryTerm) vs => theoryGroundImages vs s
interp lang::translate_variables := fun (m : TheoryMorphism) (vs : List (Name × Ty)) =>
  vs.map fun (n, t) => (n, m.type t)

impl theory_variable_images: lang::theory_variable_images for (m : TheoryMorphism)
    (s : Name → Option TheoryTerm) (vs : List (Name × Ty)) {
  m := m,
  s := s,
  variables := vs,
  accepted? := theoryGroundImages vs s,
  remaining := theoryRemainingVariables vs s,
  translated := vs.map fun (n, t) => (n, m.type t),
} by
  intro m s vs _
  cases vs with
  | nil => simp [fren_spec, theoryGroundImages, theoryRemainingVariables]
  | cons v vs =>
    rcases v with ⟨n, ty⟩
    cases h : s n <;> simp [fren_spec, theoryGroundImages, theoryRemainingVariables, List.headD, h]

interp lang::theory_terms_empty? := fun (ts : List TheoryTerm) => ts.isEmpty
interp lang::theory_first_term := fun (ts : List TheoryTerm) => ts.headD default
interp lang::theory_terms_rest := fun (ts : List TheoryTerm) => ts.tail
interp lang::theory_no_terms := fun (_ : List TheoryTerm) => ([] : List TheoryTerm)
interp lang::theory_add_term := fun (t : TheoryTerm) ts => t :: ts
interp lang::translate_terms := fun (m : TheoryMorphism) (ts : List TheoryTerm) => ts.map (·.translate m)
interp lang::substitute_terms := fun (s : Name → Option TheoryTerm) (vs : List (Name × Ty)) (ts : List TheoryTerm) =>
  ts.map (·.substitute (theorySubstitution vs s))

impl theory_term_list: lang::theory_term_list for (m : TheoryMorphism) (s : Name → Option TheoryTerm)
    (vs : List (Name × Ty)) (ts : List TheoryTerm) {
  m := m,
  s := s,
  variables := vs,
  terms := ts,
  translated := ts.map (·.translate m),
  substituted := ts.map (·.substitute (theorySubstitution vs s)),
} by
  intro m s vs ts _
  cases ts <;> simp [fren_spec, List.headD]

def role : TheorySentenceRole → lang.SentenceRole
  | .domain => .Domain
  | .theorem => .Theorem
  | .axiom => .Axiom
  | .goal => .Goal

def ofRole : lang.SentenceRole → TheorySentenceRole
  | .Domain => .domain
  | .Theorem => .theorem
  | .Axiom => .axiom
  | .Goal => .goal

@[simp] theorem ofRole_role (r : TheorySentenceRole) : ofRole (role r) = r := by cases r <;> rfl

interp lang::theory_sentence_role := fun (s : TheorySentence) => role s.role
interp lang::theory_sentence_variables := TheorySentence.variables
interp lang::theory_sentence_domain := TheorySentence.domain
interp lang::theory_sentence_calls := TheorySentence.calls
interp lang::theory_sentence_claims := TheorySentence.claims
interp lang::theory_sentence := fun r vs d cs es => TheorySentence.mk (ofRole r) vs d cs es

impl theory_translation: lang::theory_translation for (m : TheoryMorphism) (s : TheorySentence) {
  m := m,
  sentence := s,
  translated := s.translate m,
} by
  intro m s _
  simp [fren_spec, TheorySentence.translate]

impl theory_instance: lang::theory_instance for (s : TheorySentence) (images : Name → Option TheoryTerm) {
  s := images,
  sentence := s,
  accepted? := (s.instantiate images).isSome,
  instance_sentence := (s.instantiate images).getD s,
} by
  intro s images _
  by_cases h : theoryGroundImages s.variables images <;>
    simp [fren_spec, TheorySentence.instantiate, h]

interp lang::generic_morphism := fun (args : Fren.Seq Ty) (items : TheoryMorphism) =>
  genericMorphism args.toList.toArray items

impl generic_type_image: lang::generic_type_image for (args : List Ty) (items : TheoryMorphism) (ty : Ty) (n : Name) {
  arguments := Fren.Seq.ofList args,
  items := items,
  ty := ty,
  name := n,
  image := (genericMorphism args.toArray items).type ty,
  item_image := (genericMorphism args.toArray items).item n,
} by
  intro args items ty n _
  simp [fren_spec, genericMorphism]

impl generic_translation: lang::generic_translation for (args : List Ty) (items : TheoryMorphism) (s : TheorySentence) {
  arguments := Fren.Seq.ofList args,
  items := items,
  sentence := s,
  instance_sentence := genericTranslation args.toArray items s,
} by
  intro args items s _
  simp [fren_spec, genericTranslation, TheorySentence.translate]

end Fren.Impls.Theories
