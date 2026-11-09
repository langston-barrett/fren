# Writing the Fren 2 specification

The [reference style guide](../../Reqs/dev/Style.md) supplies the audience,
register, stable rule identifiers and checked-block conventions. The chapter
shape below specializes its section order for the Fren2 specification.
[Core typing](../Language/Types.md) is the template for Language chapters.

## Chapter shape

Define semantic objects before judgments and judgments before their rules,
as in chapter 4 of [The Definition of Standard ML (Revised)](https://smlfamily.github.io/sml97-defn.pdf).
Use the [FLS](https://rust-lang.github.io/fls/general.html#subchapter-segments)
style of numbered paragraphs: each normative paragraph starts with a stable
`r[...]` line. The identifier names the rule rather than its ordinal position.
Retain an existing identifier when its meaning survives a rewrite.

A Language chapter has these parts, omitting empty ones:

1. An introduction states the domain and links its prerequisites.
2. Semantic objects define identities, types, contexts and environments.
3. Abstract forms and judgment forms define the objects being related and
   the meaning of each judgment's inputs and outputs.
4. Numbered rules give premises, conclusion and side conditions. Each
   expression constructor has its own rule paragraph. Fren blocks supply
   their precise definitions.
5. Properties state consequences as Fren expectation blocks wherever
   possible, one numbered rule per property. State properties requiring
   induction even when their evidence is open.
6. Optional representations explain how finite witnesses encode the
   judgment, after the judgment itself has been defined.
7. Checked examples instantiate the rules, including rejected premises.

The semantic-object, judgment and rule headings serve as their segment
labels in this template; repeated bold labels are unnecessary. A chapter
about typing need not invent a dynamic-semantics section. Resolution,
typing and verification/definedness are judgments within static semantics.
Verification hypotheses are discharged by SMT. Dynamic semantics applies
only to well-typed, verified programs; it defines no undefined behavior and
does not prescribe evaluation order. Source constructs are defined
by derived forms translating to the typed Core.

## Semantic objects

Write contexts conventionally, as snoc sequences: `·` is empty and `Γ, τ`
extends Γ by one newest entry. A local names its entry by de Bruijn level,
counted from the oldest entry, so extending a context leaves every existing
level unchanged. When a production representation numbers entries
differently, such as nearest first, state the conversion as part of the
refinement relation to that representation rather than leaving it implicit.

Choose representations whose well-formedness holds by construction instead
of stating a validity predicate. An environment is a finite map, written as
a snoc sequence of bindings whose lookup returns the newest binding, so each
key has at most one entry and each entry has one kind.

## One-layer relations

Give a recursive position as a type parameter, for example `ExprF<E>`, with
arguments and match arms as `Snoc<E>` and `Snoc<ArmF<E>>`. This specifies
a semantic language, independently of a production IR's storage
representation. The Core syntax is shared with the dynamic semantics, so it
is complete: a literal carries its value, as in `BooleanLiteral(Bool)` and
`IntegerLiteral(Int)`. The Core is THIR after derived forms, so concrete
syntax such as parentheses has no Core form; it belongs to the Syntax
chapter.

The one-layer rule takes `ExprF<Judgment>`: each child position holds the
child's judgment, with its exact context and type. There is no separate
annotation function. A representation that names children otherwise, such
as by row position, first replaces each child by its judgment and then
calls the same rule.

Define typing by one match arm per constructor. Each arm states that
constructor's premises and side conditions. All children have derivations:
unused let values and both branches are included. A let body uses exactly
the incoming context extended by the value's type; its value uses the
incoming context. Constructor-only match patterns introduce no binder.
Compute deciding facts from forms, signatures and contexts. A caller's
success Boolean never replaces a premise that the relation can compute.

Define a derivation once as a finite tree whose every node satisfies the
one-layer rule. An optional postorder representation looks up children only
among earlier rows and calls that same rule; it must not introduce a second
set of typing decisions. Explain the source-occurrence correspondence
separately from the table's validity.

## Properties and decidability

State each property as its own global expectation block,
`expect name(params) { ... }`, with its own rule identifier and status. Small
separate obligations are easier to read and more likely to be decided. A
`proc` is for a genuine procedure, such as a primitive contract bound by
`impl`; it is never a container for properties.

Prove cheap step properties, including determinism at fixed child judgments
and context discipline, as Fren expectations. Whole-derivation uniqueness,
weakening and production-checker correspondence require their own evidence;
a layer lemma alone does not prove them. A property that needs induction
over a recursive definition may be proved in the wrapper and given a `lean`
status.

Keep every check in the decidable core: the target is no
`fren.lint.undecidable "allow"` in a chapter. Quantification over positions
of a `Seq` is outside the core; a structurally recursive function over a
snoc sequence, or a quantifier over a sequence's elements, is inside it.
Where a part cannot be decided, write a more abstract decidable version that
composes with the rest of the chapter, state the precise or
implementation-level version as a refinement of it, and state the refinement
relation. Each remaining opt-out has a one-sentence reason beside it and
names that abstract version. A lint opt-out never excuses a failed
expectation.

## Rule evidence metadata

Each rule paragraph in the template is immediately followed, before the
blank line ending it, by exactly one standalone HTML comment. Its syntax is
`<!-- status: STATUS -->`, where STATUS is exactly one of:

- `definition`: an introduction, form, relation or rule defining the language.
- `smt`: a Fren expectation proved by the chapter's checker.
- `lean THEOREM`: a fully qualified theorem name in the wrapper or an
  implementation file, compiling without `sorry`.
- `tested TEST`: a concrete test name whose source cites the rule ID.
- `open`: a stated property lacking the evidence above.

THEOREM and TEST are single non-whitespace tokens; the literal uppercase
placeholders are replaced by their names. There is one space after the colon
and one before `-->`. The comment is metadata, not part of the rule's prose
or the requirement links on its `r[...]` line. Keep those links in the
existing format so the book renderer and `impl` bindings continue to resolve.
A definition status asserts no theorem. A tested status asserts no universal
proof. An open property remains a specification obligation. Detailed coverage
inventories and implementation limits belong in
[development coverage](../../../docs/fren2-specification-coverage.md).

## Evidence outside the reference

Specification Markdown contains prose and Fren, with no Lean declarations,
proofs or Lean code fences. Put Lean statements and proofs in the chapter's
`.lean` wrapper or implementation files. Associate them with the Markdown
using rule IDs and the theorem names in status metadata. Wrappers elaborate
`#fren_md` and run `#fren_check`; every expectation must pass. Keep genuine
`impl` bindings where they already live and ensure they still resolve.

A compiler IR chapter defines its datatypes, printed form, well-formedness
and generator guarantees. A compiler pass chapter states its transformation
and preservation properties. Semantic datatypes in Fren are appropriate for
Language definitions and independently checked contracts. They do not replace
proofs or tests of production code. Compiler correspondence laws concern the
actual deciding implementation, stated in Lean or as Fren contracts bound by
`impl`. Do not introduce a copied executable pass as evidence about that code.

Test the actual code directly with Plausible, including ill-typed and partial
inputs, and report premise counts. Prove laws in Lean where cheap; use a
structural induction or fold theorem where one is available. Independent
primitive contracts fix facts such as lookup and operator meanings. Neither
roundtrips nor model agreement replace those facts. Testing is not a proof
and supplies no `impl ... by plausible` or `sorry`.
