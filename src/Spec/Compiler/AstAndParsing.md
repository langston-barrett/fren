# AST and parsing

Parsing turns source text into a tree of its written forms. The lossless
syntax tree (AST) retains names, punctuation, parentheses, comments and
whitespace, so that tools can reproduce the source and locate each
occurrence. Name resolution and type checking produce later intermediate
representations (IRs); parsing alone establishes neither the meaning of a
program nor the validity of a check.

Each rule's status comment says how it is established, as the
[style guide](../dev/Style.md#rule-evidence-metadata) defines; a `tested`
status names a check of the parser's tests.

## Source forms

The source grammar is specified in the language reference.
[Lexical structure](../Language/LexicalStructure.md) defines source text,
its tokens, trivia and rejected text, and [Syntax](../Language/Syntax.md)
the declarations and expressions that the parser accepts and their
abstract syntax trees.

r[parsing.grammar.acceptance]
The shared parser accepts exactly the texts that the grammar of
[Syntax](../Language/Syntax.md) accepts, independently of name resolution,
typing and solver verdicts.
<!-- status: tested Spec.Language.Syntax.grammar_agrees -->

r[parsing.grammar.trees]
The parser's tree of an accepted text, without parentheses and trivia, is
the abstract syntax tree that `syntax.tree.productions` gives, with its
written grouping and order.
<!-- status: tested Spec.Language.Syntax.roundtrip_agrees -->

## One parser and its entries

Each driver hands Fren text to the same parser, with an entry category.

r[parsing.shared.entry]
The parser's entry categories are one parser: the file and context
categories read a `File` and give the same tree or the same diagnostic
for the same text and file identity, and the expression category reads an
`ExpressionEntry`. Each consumes its whole input.
<!-- status: tested FrenParseTests.entriesAgree -->

r[parsing.shared.drivers]
Every driver of Fren 2 text, the command line and the hosted reader of
Markdown blocks, calls this parser, and given identical Fren text, entry
category and file identity obtains the same tree or the same diagnostic,
before host positions are translated. Extraction from a host document is
separate from parsing: delimiters of the host are not Fren tokens.
<!-- status: open -->

## Source ownership and locations

The lossless tree owns each byte of its source exactly once.

r[parsing.lossless.ownership]
The parse result retains the immutable source and an ordered partition of
its bytes into the pieces of `lexical.piece.longest`, as nonempty token,
trivia or rejected-text slices, with no gaps or duplicated ownership,
including leading and trailing trivia.
<!-- status: tested FrenParseTests.audit -->

r[parsing.tree.structure]
The AST exposes structured declarations, expressions and their ordered
children, with written names and a token reference for each occurrence:
its terminals, in order, are exactly the lexer's tokens.
<!-- status: tested FrenParseTests.coherent -->

r[parsing.source.bounds]
Every slice and diagnostic span has the source file identity and ordered
half-open UTF-8 byte offsets within that source's byte length.
<!-- status: tested FrenParseTests.audit -->

r[parsing.source.utf8]
The parser reads source text as `lexical.source.encoding` defines it.
Token, trivia and diagnostic endpoints lie on character boundaries, with
the end of input at the byte length, and invalid bytes fail before any
tree is built.
<!-- status: tested FrenParseTests.audit -->

> **Note:** Tree nodes may reference or enclose slices, so the span of a
> node may overlap its children's spans without owning their bytes a
> second time. Two uses of `base` are separate occurrences even when later
> IRs share structure. These rules fix no constructors or storage layout.
> For `aéz`, the UTF-8 byte length is 4 and `é` occupies `[1, 3)`; `[2, 2)`
> is within bounds but inside `é`, so bounds alone do not make a character
> boundary.

## Complete input and failure

A parse result distinguishes success from failure.

r[parsing.complete]
Success accounts for every input byte and contains a complete tree of the
selected entry category, with no missing or rejected syntax.
<!-- status: tested FrenParseTests.audit -->

r[parsing.failure]
Malformed input, including truncated input such as `pub fn f(` or
`let x :=`, and input of trivia alone for the expression category, gives a
failure with a diagnostic: no exception, no silently dropped token, no
invented token and no success on a proper prefix of the input. A failure
keeps every byte of the input, and is never passed on as a complete tree.
<!-- status: tested FrenParseTests.audit -->

r[parsing.determinism]
For fixed text, entry category and file identity, parsing terminates with
the same result, tree and diagnostic.
<!-- status: lean FrenParse.deterministic -->

r[parsing.diagnostic.anchor]
A syntax diagnostic is at the first token, rejected text or end of input
where the grammar cannot continue, and says what was expected there. A
missing `}`, or an arm that ends at `=>`, is reported at the end of input
with the empty span `[size, size)`; an extra `}` after a valid
declaration, at that `}`; and rejected text, at its bytes.
<!-- status: tested FrenParseTests.audit -->

The [Syntax](../Language/Syntax.md) chapter's rejected examples state
their diagnostics, which its wrapper checks.

## Reconstruction

Emission reconstructs the source from the lossless tree.

r[parsing.roundtrip]
Emitting a successful parse reproduces the original bytes, and parsing
those bytes again, with the same entry category and file identity, gives
the same tree, token spellings and trivia.
<!-- status: tested FrenParseTests.audit -->

> **Note:** Emission is reconstruction, not formatting or serialization of
> an IR. A failure also reconstructs its input, but is not a successful
> parse. Printing an abstract syntax tree is `syntax.property.unambiguous`.
> Resolution later replaces written names with item identities and de
> Bruijn indices using the [binding contracts](Bindings.md); those
> references do not replace written names in the AST.

## Byte classification

Two byte classes let the lexer and the boundary checks work on bytes.

r[parsing.primitive.space] spec::parsing::space_case::classification
A byte is whitespace exactly when it encodes a character of
`spec::lexical::WHITESPACE`: space, tab, LF or CR.
<!-- status: lean FrenParse.spaceByte_iff -->

```fren
pub mod spec
pub mod spec::parsing

pub proc space_case(byte: Nat): (space?) {
    require byte_bound: byte < 256
    ensure classification: space? iff byte is 32 | 9 | 10 | 13
}
```

r[parsing.primitive.continuation] spec::parsing::continuation_case::classification
A UTF-8 continuation byte is in the inclusive interval 128 through 191.
<!-- status: lean FrenParse.continuationByte_iff -->

```fren
pub proc continuation_case(byte: Nat): (continuation?) {
    require byte_bound: byte < 256
    ensure classification: continuation? iff 128 <= byte < 192
}
```

r[parsing.primitive.boundary]
In valid UTF-8, an offset inside the text is a character boundary exactly
when its byte is not a continuation byte; 0 and the byte length are
boundaries too.
<!-- status: open -->
