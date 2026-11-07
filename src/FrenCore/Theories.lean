-- keep-sorted start
import FrenCore.Definitions
import FrenCore.Ty
import FrenCore.TypeSubstitution
-- keep-sorted end

/-!
# Theories (`Reqs/Lang/ModulesAndInterfaces`, `Reqs/Lang/Implementations`)

The common representation for modules, generic functions and generic types.
Generic function instances translate their references through it, and generic
datatypes extract their constructor declarations into it. Module adoption
continues in #761. A morphism translates types and signature items uniformly,
including constants for unspecified values. Ground instantiation is
simultaneous and keeps the sentence's domain, calls and claims together.
Choosing substitutions by matching, closing a query under instances, and
discharging a morphism's obligations are separate operations, not implemented
here.
-/

namespace Fren.Core

open Lean (Name)

/-- Signature declarations. A datatype's freeness belongs to its declaration,
not to an extra axiom (`module.generic-type.sentences`). -/
inductive TheoryDeclarationKind where
  | type | datatype | constructor | constant | function | procedure | implementation
  deriving Inhabited, DecidableEq

/-- One parameter or item. `types` records its argument and result types;
front ends retain their full declaration alongside this signature entry. -/
structure TheoryDeclaration where
  name : Name
  kind : TheoryDeclarationKind
  abstract : Bool
  types : List Ty := []
  deriving Inhabited, BEq

/-- Sentence parameters, local quantifier indices, and query locals occupy
separate namespaces. Applications are curried; sorts also represent explicit
type arguments. Builtins and literals are not signature items. Definitions of
local aliases and constants must be expanded before matching, not by unfolding
function bodies (`module.instance.matching`). -/
inductive TheoryTerm where
  | variable (name : Name)
  | bound (index : Nat)
  | query (name : Name)
  | item (name : Name)
  | literal (text : String)
  | sort (type : Ty)
  | app (function argument : TheoryTerm)
  | all (type : Ty) (body : TheoryTerm)
  | ex (type : Ty) (body : TheoryTerm)
  deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

/-- Visit references in the shared theory syntax. Applied item heads are
opaque; query aliases and unapplied item constants can be expanded. -/
def TheoryTerm.expandDefinitions (lookup : TheoryTerm → TheoryTerm → TheoryTerm) : TheoryTerm → TheoryTerm
  | .app (.item n) a => .app (.item n) (a.expandDefinitions lookup)
  | .app f a => .app (f.expandDefinitions lookup) (a.expandDefinitions lookup)
  | .all ty b => .all ty (b.expandDefinitions lookup)
  | .ex ty b => .ex ty (b.expandDefinitions lookup)
  | t@(.query _) | t@(.item _) => lookup t t
  | t => t

instance : DefinitionSyntax TheoryTerm TheoryTerm := ⟨TheoryTerm.expandDefinitions⟩

/-- A type and item map supplied by a resolved morphism. Images belong to the
target signature: translation does not translate them again. Mapping types
includes their type arguments (for generics, e.g. `Ty.subst`). Checking that
these maps preserve declarations is part of implementation checking. -/
structure TheoryMorphism where
  type : Ty → Ty := id
  item : Name → Name := id
  deriving Inhabited

/-- Translate a signature declaration, preserving its kind and abstractness
(`lang::theory_declaration_translation`). Constructor types translate just
like the types of functions and constants. -/
def TheoryDeclaration.translate (d : TheoryDeclaration) (m : TheoryMorphism) : TheoryDeclaration :=
  { d with name := m.item d.name, types := d.types.map m.type }

/-- The type morphism of a generic instance. Substitution is simultaneous,
including within other datatype instances (`lang::instantiation`). -/
def genericTypeMorphism (args : Array Ty) : TheoryMorphism :=
  { type := (·.subst args) }

/-- A generic datatype's constructor or field declaration at its type
arguments. Datatype freeness stays in the declaration; instantiation adds
no axiom (`module.generic-type.sentences`). -/
def instantiateTypeDeclaration (d : TheoryDeclaration) (args : Array Ty) : TheoryDeclaration :=
  d.translate (genericTypeMorphism args)

/-- Structural translation along a morphism (`implementation.morphism`). -/
def TheoryTerm.translate (m : TheoryMorphism) : TheoryTerm → TheoryTerm
  | .item n => .item (m.item n)
  | .sort t => .sort (m.type t)
  | .app f a => .app (f.translate m) (a.translate m)
  | .all t b => .all (m.type t) (b.translate m)
  | .ex t b => .ex (m.type t) (b.translate m)
  | .variable n => .variable n
  | .bound k => .bound k
  | .query n => .query n
  | .literal s => .literal s

/-- Whether a query term has no sentence parameter and no reference to a
binder outside itself (`module.instance.ground`). Query locals are ground.
A term closed by its own quantifiers is ground too. -/
def TheoryTerm.ground (depth : Nat := 0) : TheoryTerm → Bool
  | .variable _ => false
  | .bound k => k < depth
  | .app f a => f.ground depth && a.ground depth
  | .all _ b | .ex _ b => b.ground (depth + 1)
  | _ => true

/-- Simultaneous substitution of sentence parameters. Only ground images are
accepted by `TheorySentence.instantiate`; the separate query and bound
constructors then prevent capture beneath the sentence's quantifiers.
Absent images stay quantified (`module.binding.outside`). -/
def TheoryTerm.substitute (terms : Name → Option TheoryTerm) : TheoryTerm → TheoryTerm
  | .variable n => (terms n).getD (.variable n)
  | .app f a => .app (f.substitute terms) (a.substitute terms)
  | .all t b => .all t (b.substitute terms)
  | .ex t b => .ex t (b.substitute terms)
  | t => t

inductive TheorySentenceRole where
  | domain | theorem | axiom | goal
  deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

/-- One sentence: universally quantified parameters, a domain, the relations
of its calls, and its claims. Its meaning is `domain ∧ calls ⇒ claims`
(`module.meaning`); instantiation preserves all three parts. -/
structure TheorySentence where
  role : TheorySentenceRole
  variables : List (Name × Ty)
  domain : TheoryTerm
  calls : List TheoryTerm
  claims : List TheoryTerm
  deriving Inhabited, BEq, DecidableEq, ReflBEq, LawfulBEq

/-- Translate every type and term of a sentence by the same morphism. Its
role is preserved; turning translated laws into obligations or trusted axioms
belongs to the implementation checker (`implementation.obligations`). -/
def TheorySentence.translate (s : TheorySentence) (m : TheoryMorphism) : TheorySentence :=
  { s with
    variables := s.variables.map fun (n, t) => (n, m.type t)
    domain := s.domain.translate m
    calls := s.calls.map (·.translate m)
    claims := s.claims.map (·.translate m) }

/-- Whether every supplied parameter image is ground. Undeclared images
are ignored, as they are by `theorySubstitution`. -/
def theoryGroundImages (variables : List (Name × Ty)) (terms : Name → Option TheoryTerm) : Bool :=
  variables.all fun (n, _) => (terms n).all (·.ground)

/-- The parameters without images, with their original names and types. -/
def theoryRemainingVariables (variables : List (Name × Ty)) (terms : Name → Option TheoryTerm) : List (Name × Ty) :=
  variables.filter fun (n, _) => (terms n).isNone

/-- Restrict a substitution to the sentence's declared parameters. -/
def theorySubstitution (variables : List (Name × Ty)) (terms : Name → Option TheoryTerm) (n : Name) : Option TheoryTerm :=
  if variables.any (·.1 == n) then terms n else none

/-- One instance at query terms (`module.instance`, `module.instance.hypothesis`).
Names without images retain their original identity and type, so removing one
parameter does not renumber the others. An image for an undeclared name is
ignored. The consumer supplies a well-scoped sentence and type-correct
query terms; this operation checks that the terms are ground. -/
def TheorySentence.instantiate (s : TheorySentence) (terms : Name → Option TheoryTerm) : Option TheorySentence := do
  if !theoryGroundImages s.variables terms then none else
    let declared := theorySubstitution s.variables terms
    some { s with
      variables := theoryRemainingVariables s.variables terms
      domain := s.domain.substitute declared
      calls := s.calls.map (·.substitute declared)
      claims := s.claims.map (·.substitute declared) }

inductive TheoryEntry where
  | declaration (item : TheoryDeclaration)
  | sentence (claim : TheorySentence)
  deriving Inhabited

structure Theory where
  parameters : List TheoryDeclaration
  entries : List TheoryEntry
  deriving Inhabited

structure TheorySignature where
  parameters : List TheoryDeclaration
  items : List TheoryDeclaration
  deriving Inhabited

/-- Drop sentence entries, retaining declarations in their original order. -/
def theorySignatureItems (entries : List TheoryEntry) : List TheoryDeclaration :=
  entries.filterMap fun | .declaration d => some d | .sentence _ => none

/-- Parameters and non-sentence items, in declaration order
(`module.theory`, `module.signature`). -/
def Theory.signature (t : Theory) : TheorySignature :=
  { parameters := t.parameters
    items := theorySignatureItems t.entries }

end Fren.Core
