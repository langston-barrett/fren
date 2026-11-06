-- keep-sorted start
import FrenCore.Generics
import FrenCore.Theories
-- keep-sorted end

/-! Regressions for the shared theory core and generic function morphisms. -/
-- fren-covers: lang::theory_signature, lang::theory_translation, lang::theory_instance
-- fren-covers: lang::theory_term_translation, lang::theory_term_substitution, lang::theory_ground_term
-- fren-covers: lang::theory_variable_images, lang::theory_term_list
-- fren-covers: lang::generic_type_image, lang::generic_translation

open Fren.Core

namespace FrenTest.Theories

private def sentence : TheorySentence := {
  role := .axiom
  variables := [(`x, .param 0 `T), (`y, .seq (.param 0 `T)), (`outside, .int)]
  domain := .app (.item `require) (.variable `x)
  calls := [.app (.app (.item `call) (.variable `x)) (.variable `y)]
  claims := [
    .app (.app (.item `eq) (.app (.item `f) (.variable `x))) (.item `unspecified),
    .all (.param 0 `T) (.ex (.set (.param 0 `T))
      (.app (.app (.variable `outside) (.bound 1)) (.bound 0))),
    .app (.app (.item `f) (.sort (.seq (.param 0 `T)))) (.literal "0")]
}

private def morphism : TheoryMorphism := {
  type := fun t => t.subst #[.int]
  item := fun n => if n == `f then `g else if n == `g then `h
    else if n == `unspecified then `instance.unspecified
    else if n == `call then `implementedCall
    else if n == `require then `requireAtInstance else n
}

-- Translate domain, calls, claims, parameter types and inner binder sorts.
-- Images are simultaneous: f maps to g, not h. Builtins stay literal.
#guard (sentence.translate morphism).role == .axiom
#guard (sentence.translate morphism).variables == [(`x, .int), (`y, .seq .int), (`outside, .int)]
#guard (sentence.translate morphism).domain == .app (.item `requireAtInstance) (.variable `x)
#guard (sentence.translate morphism).calls == [
  .app (.app (.item `implementedCall) (.variable `x)) (.variable `y)]
#guard (sentence.translate morphism).claims == [
  .app (.app (.item `eq) (.app (.item `g) (.variable `x))) (.item `instance.unspecified),
  .all .int (.ex (.set .int) (.app (.app (.variable `outside) (.bound 1)) (.bound 0))),
  .app (.app (.item `g) (.sort (.seq .int))) (.literal "0")]
#guard sentence.translate {} == sentence

-- A function instance translates every reference together, including
-- nested sorts, inner quantifiers, unspecified values and recursive calls.
-- A second map for item types cannot override the inferred type arguments.
#guard genericTranslation #[.int] { morphism with type := fun _ => .bool } sentence == sentence.translate morphism
#guard (genericMorphism #[.param 1 `U, .bool]).type (.param 0 `T) == .param 1 `U
#guard (genericMorphism #[.int]).type (.param 2 `V) == .param 2 `V
#guard (genericMorphism #[.int]).type (.record `R [.seq (.param 0 `T), .set (.param 0 `T)]) ==
  .record `R [.seq .int, .set .int]
#guard (TheoryTerm.query `f).translate morphism == .query `f
#guard (TheoryTerm.variable `f).translate morphism == .variable `f
#guard (TheoryTerm.literal "f").translate morphism == .literal "f"
#guard (TheoryTerm.bound 0).translate morphism == .bound 0

private def terms : Lean.Name → Option TheoryTerm
  | `x => some (.query `outside)
  | `y => some (.app (.item `ys) (.literal "1"))
  | `notDeclared => some (.bound 0)
  | _ => none

private def expected : TheorySentence := {
  sentence with
  variables := [(`outside, .int)]
  domain := .app (.item `require) (.query `outside)
  calls := [.app (.app (.item `call) (.query `outside)) (.app (.item `ys) (.literal "1"))]
  claims := [
    .app (.app (.item `eq) (.app (.item `f) (.query `outside))) (.item `unspecified),
    sentence.claims[1]!,
    sentence.claims[2]!]
}

-- A variable without an image keeps its identity; replacing earlier ones
-- must not renumber it. Ground query locals remain free under quantifiers.
#guard sentence.instantiate terms == some expected
#guard sentence.instantiate (fun _ => none) == some sentence
#guard ({ sentence with claims := [.all .int (.app (.variable `x) (.bound 0))] }.instantiate terms).map
    TheorySentence.claims == some [.all .int (.app (.query `outside) (.bound 0))]

-- An external query binder or another sentence parameter is not ground.
-- Checking both branches of an application and under both quantifiers matters.
#guard sentence.instantiate (fun _ => some (.bound 0)) == none
#guard sentence.instantiate (fun _ => some (.variable `y)) == none
#guard sentence.instantiate (fun _ => some (.app (.bound 0) (.literal "0"))) == none
#guard sentence.instantiate (fun _ => some (.app (.item `f) (.bound 0))) == none
#guard sentence.instantiate (fun _ => some (.all .int (.bound 1))) == none
#guard sentence.instantiate (fun _ => some (.ex .int (.bound 1))) == none
#guard sentence.instantiate (fun _ => some (.all .int (.ex .int (.bound 1)))) |>.isSome
#guard sentence.instantiate (fun _ => some (.all .int (.bound 0))) |>.isSome

-- Inserting a query local with another parameter's name must not apply
-- that parameter's substitution to the newly inserted term.
private def simultaneous : Lean.Name → Option TheoryTerm
  | `x => some (.query `y)
  | `y => some (.literal "2")
  | _ => none

#guard ({ sentence with claims := [.app (.variable `x) (.variable `y)] }.instantiate simultaneous).map
    TheorySentence.claims == some [.app (.query `y) (.literal "2")]

-- An undeclared image is ignored, including when it is not ground.
#guard ({ sentence with variables := [], claims := [.variable `notDeclared] }.instantiate terms).map
    TheorySentence.claims == some [.variable `notDeclared]

-- Translation and instantiation do not reclassify a sentence. In particular,
-- deciding which translated laws are obligations is a later operation.
#guard ([.domain, .theorem, .axiom, .goal] : List TheorySentenceRole).all fun r =>
  ({ sentence with role := r }.translate morphism).role == r
#guard ([.domain, .theorem, .axiom, .goal] : List TheorySentenceRole).all fun r =>
  ({ sentence with role := r }.instantiate terms).map TheorySentence.role == some r

private def declarations : List TheoryDeclaration := [
  { name := `T, kind := .type, abstract := true },
  { name := `Option, kind := .datatype, abstract := false, types := [.param 0 `T] },
  { name := `Some, kind := .constructor, abstract := false, types := [.param 0 `T] },
  { name := `unspecified, kind := .constant, abstract := false },
  { name := `f, kind := .function, abstract := true },
  { name := `p, kind := .procedure, abstract := true }]

private def theory : Theory := {
  parameters := [{ name := `Self, kind := .type, abstract := true },
    { name := `bound, kind := .implementation, abstract := true }]
  entries := [.sentence sentence, .declaration declarations[0]!,
    .sentence { sentence with role := .goal }] ++
    (declarations.drop 1).map TheoryEntry.declaration ++
    [.sentence { sentence with role := .theorem }, .sentence { sentence with role := .domain }]
}

-- Filtering keeps every declaration and parameter exactly, in order, even
-- when sentences surround or precede them; datatypes introduce no new axiom.
#guard theory.signature.parameters == theory.parameters
#guard theory.signature.items == declarations
#guard ({ parameters := [], entries := [] } : Theory).signature.items.isEmpty
#guard theory.entries.length == declarations.length + 4

end FrenTest.Theories
