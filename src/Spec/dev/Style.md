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

1. An introduction states the domain and links its prerequisites. A chapter
   that defines syntax gives its grammar in the usual notation, and a
   chapter of rules gives an informative figure of all of them, in the
   notation of The Definition of Standard ML; the numbered rules remain
   normative.
2. Semantic objects define identities, types, contexts and environments.
3. Abstract forms and judgment forms define the objects being related and
   the meaning of each judgment's inputs and outputs.
4. Numbered rules give premises, conclusion and side conditions. Each
   expression constructor has its own rule paragraph, followed by the Fren
   function that states it, one premise per line.
5. Properties state the chapter's headline metatheorems: for typing, at
   least determinism, weakening, well-scopedness and safety with respect to
   the dynamic semantics. State a property even when its evidence is open.
6. Representations explain how finite witnesses encode the judgment, after
   the judgment itself has been defined.
7. Examples instantiate the rules, including rejected premises.

Every normative paragraph, examples included, starts with an `r[...]` line
and has a status. Every Fren definition is reachable from a rule's links.
Material that a later chapter will own sits in a clearly marked section
that names that chapter.

The semantic-object, judgment and rule headings serve as their segment
labels in this template; repeated bold labels are unnecessary. A chapter
about typing need not invent a dynamic-semantics section. Resolution,
typing and verification/definedness are judgments within static semantics.
Verification hypotheses are discharged by SMT. Dynamic semantics applies
only to well-typed, verified programs; it defines no undefined behavior and
does not prescribe evaluation order. Source constructs are defined
by derived forms translating to the typed Core, and a source program is
well typed exactly when its translation is.

## Semantic objects

Write contexts conventionally, as snoc sequences: `·` is empty and `Γ, τ`
extends Γ by one newest entry. A local names its entry by de Bruijn level,
counted from the oldest entry, so extending a context leaves every existing
level unchanged.

Choose representations whose well-formedness holds by construction where
the language allows it. Where the language makes something an error, such
as binding an item twice, do not hide it in the representation: state the
invariant that the earlier judgment guarantees, such as resolution
rejecting duplicates, and a well-formedness predicate that checks it. Types
and environments have well-formedness conditions: a nominal type names an
enumeration, and every constructor's owner lists it.

## One-layer relations

Give a recursive position as a type parameter, for example `ExprF<E>`, with
arguments and match arms as `Snoc<E>` and `Snoc<ArmF<E>>`. Say in one plain
sentence why: Fren cannot yet declare a datatype that contains itself inside
another type. Record that limit and the feature that would remove it in the
development coverage document. The Core syntax is shared with the dynamic
semantics, so it is complete: a literal carries its value, and a let carries
its written type annotation. The Core is THIR after derived forms, so
concrete syntax such as parentheses, and spelling such as a `?` suffix, has
no Core form; it belongs to the Syntax or derived-forms chapter.

The one-layer rule takes `ExprF<Typing>`: each child position holds the
child's typing, with its exact context and type. Each typing rule is its own
Fren function under its paragraph, and the one-layer rule only dispatches
on the form. Compute deciding facts from forms, signatures and contexts. A
caller's success Boolean never replaces a premise that the relation can
compute. All children have derivations: unused let values and both branches
are included.

Define a derivation once, as a finite tree whose every node satisfies the
one-layer rule, and give it a Fren definition over whatever witness Fren
can express, such as a postorder table whose rows look up children only
among earlier rows and call the same rule. State the metatheorems over that
witness rather than leaving them in prose.

## Properties and decidability

State each family of properties as one global expectation block,
`expect name(params) { ... }`, with one rule identifier and status and a
named claim per case, and cite the claims as `name::{a, b}`. Do not add an
aggregate rule that only restates its parts. A `proc` is for a genuine
procedure; it is never a container for properties. Prefer properties that
say something about the type system, such as inversion, determinism,
scoping, weakening and safety, over facts about constants.

Maximize the decidable part of a chapter, but do not contort a rule to
avoid undecidability. Quantification over positions of a `Seq` is outside
Fren's decidable core; a structurally recursive function over a snoc
sequence, or a quantifier over a sequence's elements, is inside it. Where a
rule reads better stated directly but undecidably, state it so, and give it
a decidable abstraction that composes with the rest of the chapter,
treating the direct statement as its refinement and stating the refinement
relation. Each `fren.lint.undecidable "allow"` has a one-sentence reason
beside it. A lint opt-out never excuses a failed expectation. A property
that needs induction may be proved in the wrapper and given a `lean`
status.

## Language and compiler

A Language chapter states the language. Correspondence with production
code, such as a different numbering of locals, primitive contracts bound
by `impl`, or the agreement of a checker with the judgment, belongs to the
Compiler chapter of that pass. A definition's status is never a
correspondence theorem. Limitations of today's tools, and diagnostic
positions of today's checker, belong in the development coverage document,
not in normative text.

## Examples

Precede each example with the judgment it shows, in the chapter's printed
notation, such as `Σ; · ⊢ let 1 in #0 : Integer`. Keep a few complete
witnesses in the chapter and check the rest in the wrapper, at least one for
each rule. Add `fren example` source programs, each with the diagnostic it
expects and a `--@ reference:` line for the rule it exercises.

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
`impl` bindings in the wrapper of the Compiler chapter whose contracts they
bind, and ensure they still resolve.

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
