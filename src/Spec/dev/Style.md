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
2. An overview gives the gist in one screen (see [Overview](#overview)).
3. Semantic objects define identities, types, contexts and environments,
   with their well-formedness judgments.
4. Abstract forms and judgment forms define the objects being related and
   the meaning of each judgment's inputs and outputs. A chapter that defines
   syntax gives its grammar in the usual notation.
5. Numbered rules give premises, conclusion and side conditions. Each
   expression constructor has its own rule paragraph, followed by the Fren
   function that states it, one premise per line.
6. Witnesses define the finite objects, such as derivation tables, over
   which the judgment is stated, before any property mentions them.
7. Declarations and programs lift the judgment to a whole program.
8. Properties state the chapter's headline metatheorems: for typing, at
   least determinism, decidability (an algorithm and its agreement with the
   rules), regularity (typing produces well-formed types), well-scopedness,
   weakening and safety with respect to the dynamic semantics. State a
   property even when it is open.
9. Examples instantiate the rules, including rejected premises.

Every normative paragraph, examples included, starts with an `r[...]` line.
Every Fren definition is reachable from a rule's links. A paragraph that
defines makes no claim: any sentence that could be true or false, such as
that a construction ends or that a later judgment rejects something, is a
property paragraph of its own. Material that a later chapter will own sits
in a clearly marked section that names that chapter.

The semantic-object, judgment and rule headings serve as their segment
labels in this template; repeated bold labels are unnecessary. A chapter
about typing need not invent a dynamic-semantics section. Resolution,
typing and verification/definedness are judgments within static semantics.
Verification hypotheses are discharged by SMT. Dynamic semantics applies
only to well-typed, verified programs; it defines no undefined behavior and
does not prescribe evaluation order. Source constructs are defined
by derived forms translating to the typed Core, and a source program is
well typed exactly when its translation is.

## Statements and their Fren

Each numbered rule's prose is immediately followed by the Fren that
defines or checks it, before the next rule. Several small definitions that
serve one rule stay together under it; a definition that serves many rules,
such as a sequence helper, gets a short rule of its own. No block gathers
the code of several rules. The `ruleReqs` job checks this for the chapters
that follow the template: each item of their Fren is linked by the nearest
rule before it.

## Overview

A chapter opens with an overview: a table of its judgment forms, their
meanings and the Fren that states them, and an abstract interface. The
interface declares abstract types and uninterpreted functions for the
chapter's main objects and relation, and states its key laws as their
contracts, or as expectations that the contracts prove. The chapter's
wrapper interprets each abstract type and function by its detailed
definition (`interp`), which proves the contracts for the detailed
definitions: the interpretation is the refinement relation. A law that
would be a contract on a function returning an abstract type, such as a
`weaken` that returns a derivation, cannot be one: that contract's
realizability check is outside the decidable core. Such a law links to the
property that states it below. Say exactly what a contract law states; a
derivation that records its type determines it, which is not uniqueness of
an expression's type.

## Notation

Figures and prose write types as in the language: `Bool`, `Int` and
`Nominal(a)`. They name locals, as in `let x := e₁ in e₂` and
`let x : τ := e₁ in e₂`, and say once that each name stands for a de
Bruijn level; the Fren is nameless. Each judgment's figure sits at the start
of the section or rule that defines it in Fren, in the notation of The
Definition of Standard ML, with every notation it uses defined, at most 80
columns wide. Figures are informative; the numbered rules are normative.

Fren identifiers and figures use one set of abbreviations:

| Abbreviation | Meaning | Figure |
| --- | --- | --- |
| `ty`, `Ty` | a type | τ, σ |
| `ctx`, `Ctx` | a context | Γ, Δ |
| `symb`, `Symb` | a symbol environment | Σ |
| `sig`, `Sig` | a function signature | |
| `param`, `params` | a parameter, the parameters | |
| `arg`, `args` | an argument, the arguments | aₖ |
| `decl`, `decls`, `Decl` | a declaration, the declarations | d |
| `prog` | a program | |
| `pos` | a row's position in a table | |
| `rows` | a derivation table, as a Fren value | |
| `deriv`, `Derivation` | a derivation, in an abstract interface | d |
| `form`, `Form` | a layer whose children are row positions | |
| layer | one form `ExprF<E>` with its children | l |
| `ok?` suffix | a well-formedness check | `⊢ … ok` |

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
arguments and match arms as `Snoc<E>` and `Snoc<ArmF<E>>`, and present the
rules over this one-layer view. Where `ExprF<E>` is introduced, say in one
sentence what makes the encoding possible and what the one form type is
for; record the limit of Fren behind it, and the feature that would remove
it, in the development coverage document. The Core syntax is shared with
the dynamic semantics, so it is complete: a literal carries its value, and
a let carries its written type annotation. Concrete syntax such as
parentheses, and spelling such as a `?` suffix, has no Core form; it
belongs to the Syntax or derived-forms chapter.

The one-layer rule takes `ExprF<Typing>`: each child position holds the
child's typing, with its exact context and type. Each typing rule is its own
Fren function under its paragraph, and the one-layer rule only dispatches
on the form. Compute deciding facts from forms, signatures and contexts. A
caller's success Boolean never replaces a premise that the relation can
compute. All children have derivations: unused let values and both branches
are included.

Define the judgment once, over whatever witness Fren can express, such as a
table whose rows look up children only among earlier rows and call the same
rule, and say precisely which expression a witness's root unfolds to. State
the agreement of that definition with the inductive reading of the rules as
a property of its own, and state the metatheorems over the witness rather
than leaving them in prose.

## Properties and evidence

A rule's evidence is Fren's own, so that it follows mechanically from the
rule's links and [`fren trace`](../../Reqs/Trace.md):

- A property that the solver proves is an `expect`: the check is the
  evidence. State each family as one global expectation block with a named
  claim per case, cite the claims as `name::{a, b}`, and do not add an
  aggregate rule that only restates its parts.
- A property proved in Lean is a procedure whose `ensure` states exactly
  what the Lean theorem proves, bound in the wrapper by an `impl` whose
  proof uses that theorem; `fren trace` reports it `proved`. A procedure
  without outputs takes its level from its calls, and with none would be
  reported `proved` without evidence, so a law's procedure has one output,
  `holds?`, with `ensure output: holds?`, until Fren's trace takes account
  of how a procedure's own checks ran. Put the law's hypotheses in its
  `ensure` as `when`, and set `fren.evidence` to `"random"`: this only stops
  the procedure's realizability check from asking the solver for the
  induction. Random inputs rarely meet a law's hypotheses, so do not claim
  that testing supports the law.
- A property checked by tests is a procedure with a `tested` claim naming
  the test.
- An open property that Fren can state is such a procedure with no `impl`
  and a `trusted` claim whose reason starts `open:` and says what is
  missing, so that it is open on purpose. One that Fren cannot state is
  prose that says it is open.
- A definition carries no evidence.

A converted chapter's wrapper ends with
`set_option fren.requireEvidence "trusted" in #fren_trace`, so that a
procedure that loses its evidence makes `lake build --wfail` fail. The
`ruleReqs` job checks that each chapter on its list of converted chapters
has this, and no hand-written status comments; the list grows as chapters
are converted.

Prefer properties that say something about the type system, such as
inversion, determinism, scoping, weakening and safety, over facts about
constants.

Maximize the decidable part of a chapter, but do not contort a rule to
avoid undecidability. Quantification over positions of a `Seq` is outside
Fren's decidable core; a structurally recursive function over a snoc
sequence, or a quantifier over a sequence's elements, is inside it. Where a
rule reads better stated directly but undecidably, state it so, and give it
a decidable abstraction that composes with the rest of the chapter,
treating the direct statement as its refinement and stating the refinement
relation. Every lint opt-out, of `undecidable` or any other lint, has a
one-sentence reason beside it. A lint opt-out never excuses a failed
expectation.

## Language and compiler

A Language chapter states the language; the THIR chapter refines its Core.
Correspondence with production code, such as a different numbering of
locals, primitive contracts bound by `impl`, or the agreement of a checker
with the judgment, belongs to the Compiler chapter of that pass.
Limitations of today's tools, and diagnostic positions of today's checker,
belong in the development coverage document, not in normative text.

## Examples

Precede each example with the judgment it shows, in the chapter's printed
notation, such as `Σ; · ⊢ let x : Int := 1 in x : Int`, and show its table
as numbered rows. Keep a few complete witnesses in the chapter and check the
rest in the wrapper, at least one for each rule. A rejected example claims
that no witness exists, so state it as an expectation that quantifies over
every part its premises leave free, such as the children's typings, rather
than checking one table; or say only that one table is rejected. Source
programs in `fren example` blocks, each with the diagnostic it expects and
a `--@ reference:` line for the rule it exercises, are informative until
the source-to-Core translation is specified.

## Evidence outside the reference

Specification Markdown contains prose and Fren, with no Lean declarations,
proofs or Lean code fences. Put Lean statements and proofs in the chapter's
`.lean` wrapper or implementation files, and connect them to the Markdown
through `impl` and `interp`. Wrappers elaborate `#fren_md`, run
`#fren_check`, in which every expectation must pass, and run `#fren_trace`.
Keep genuine `impl` bindings of production code in the wrapper of the
Compiler chapter whose contracts they bind, and ensure they still resolve.

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
