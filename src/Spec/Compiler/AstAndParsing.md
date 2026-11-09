# AST and parsing

Parsing turns source text into a tree of its written forms. The lossless
syntax tree (AST) retains names, punctuation, parentheses, comments and
whitespace, so that tools can reproduce the source and locate each
occurrence. Name resolution and type checking produce later intermediate
representations (IRs); parsing alone establishes neither the meaning of a
program nor the validity of a check.

Rule statuses are those of
[Lexical structure](../Language/LexicalStructure.md). A `tested` status
names the test module of the parser that checks the rule.

## Source forms

The source grammar is specified in the language reference.
[Lexical structure](../Language/LexicalStructure.md) defines source text,
its tokens, trivia and rejected text, and [Syntax](../Language/Syntax.md)
the declarations and expressions that the parser accepts and their
abstract syntax trees.

**Implementation requirements**

r[parsing.walking.forms]
status: tested Spec.Language.Syntax.grammar_agrees
The shared parser accepts exactly the texts that the grammar of
[Syntax](../Language/Syntax.md) accepts, with their written grouping and
order, independently of name resolution, typing and solver verdicts. Its
tree, without parentheses and trivia, is the abstract syntax tree that
`syntax.tree.productions` gives.

## One parser and its entries

Each driver hands Fren text to the same parser, with an entry category.

**Implementation requirements**

r[parsing.shared.entry]
status: tested FrenParseTests.Properties
The drivers call the same parser. Given identical Fren text, entry
category and file identity, they obtain the same tree or the same
diagnostic, before host positions are translated. The file and context
categories read a `File`, and the expression category an
`ExpressionEntry`; each consumes its whole input. Extraction from a host
document is separate from parsing: delimiters of the host are not Fren
tokens.

## Source ownership and locations

The lossless tree owns each byte of its source exactly once.

**Implementation requirements**

r[parsing.lossless.ownership]
status: tested FrenParseTests.Properties
The parse result retains the immutable source and an ordered partition of
its bytes into the pieces of `lexical.piece.longest`, as nonempty token,
trivia or rejected-text slices, with no gaps or duplicated ownership,
including leading and trailing trivia.

r[parsing.tree.structure]
status: tested FrenParseTests.Properties
The AST exposes structured declarations, expressions and their ordered
children, with written names and a token reference for each occurrence:
its terminals, in order, are exactly the lexer's tokens.

r[parsing.source.bounds]
status: tested FrenParseTests.Properties
Every slice and diagnostic span has the source file identity and ordered
half-open UTF-8 byte offsets within that source's byte length.

r[parsing.source.utf8]
status: tested FrenParseTests.Properties
The parser reads source text as `lexical.source.encoding` defines it.
Token, trivia and diagnostic endpoints lie on character boundaries, with
the end of input at the byte length, and invalid bytes fail before any
tree is built.

> **Note:** Tree nodes may reference or enclose slices, so the span of a
> node may overlap its children's spans without owning their bytes a
> second time. Two uses of `base` are separate occurrences even when later
> IRs share structure. These rules fix no constructors or storage layout.
> For `aéz`, the UTF-8 byte length is 4 and `é` occupies `[1, 3)`; `[2, 2)`
> is within bounds but inside `é`, so bounds alone do not make a character
> boundary.

## Complete input and failure

A parse result distinguishes success from failure.

**Implementation requirements**

r[parsing.complete]
status: tested FrenParseTests.Properties
Success accounts for every input byte and contains a complete tree of the
selected entry category, with no missing or rejected syntax.

r[parsing.failure]
status: tested FrenParseTests.Properties
Malformed input, including truncated input such as `pub fn f(` or
`let x :=`, and input of trivia alone for the expression category, gives a
failure with a diagnostic: no exception, no silently dropped token, no
invented token and no success on a proper prefix of the input. A failure
keeps every byte of the input, and is never passed on as a complete tree.

r[parsing.determinism]
status: lean FrenParse.deterministic
For fixed text, entry category and file identity, parsing terminates with
the same result, tree and diagnostic.

r[parsing.diagnostic.anchor]
status: tested FrenParseTests.Grammar
A syntax diagnostic is at the first token, rejected text or end of input
where the grammar cannot continue, and says what was expected there. A
missing `}`, or an arm that ends at `=>`, is reported at the end of input
with the empty span `[size, size)`; an extra `}` after a valid
declaration, at that `}`; and rejected text, at its bytes.

**Examples**

The [Syntax](../Language/Syntax.md) chapter's rejected examples state
their diagnostics, which its wrapper checks.

## Reconstruction

Emission reconstructs the source from the lossless tree.

**Implementation requirements**

r[parsing.roundtrip]
status: tested FrenParseTests.Properties
Emitting a successful parse reproduces the original bytes, and parsing
those bytes again, with the same entry category and file identity, gives
the same tree, token spellings and trivia.

> **Note:** Emission is reconstruction, not formatting or serialization of
> an IR. A failure also reconstructs its input, but is not a successful
> parse. Printing an abstract syntax tree is `syntax.print.roundtrip`.
> Resolution later replaces written names with item identities and de
> Bruijn indices using the [binding contracts](Bindings.md); those
> references do not replace written names in the AST.

## Byte classification

Two byte classes let the lexer and the boundary checks work on bytes.

**Implementation requirements**

r[parsing.primitive.space] spec::parsing::space_case::{classification, space, tab, lf, cr, ordinary}
status: lean FrenParse.spaceByte_iff
A byte is whitespace exactly when it encodes a character of
`spec::lexical::WHITESPACE`: space, tab, LF or CR.

```fren
pub mod spec
pub mod spec::parsing

pub proc space_case(byte: Nat): (space?) {
    require byte_bound: byte < 256
    ensure classification: space? iff byte is 32 | 9 | 10 | 13

    expect space: when byte = 32, space?
    expect tab: when byte = 9, space?
    expect lf: when byte = 10, space?
    expect cr: when byte = 13, space?
    expect ordinary: when byte = 97, not space?
}
```

r[parsing.primitive.continuation] spec::parsing::continuation_case::{classification, first, last, ascii, lead}
status: lean FrenParse.continuationByte_iff
A UTF-8 continuation byte is in the inclusive interval 128 through 191.
In valid UTF-8, an offset inside the text is a character boundary exactly
when its byte is not a continuation byte; 0 and the byte length are
boundaries too.

```fren
pub proc continuation_case(byte: Nat): (continuation?) {
    require byte_bound: byte < 256
    ensure classification: continuation? iff 128 <= byte < 192

    expect first: when byte = 128, continuation?
    expect last: when byte = 191, continuation?
    expect ascii: when byte < 128, not continuation?
    expect lead: when byte >= 192, not continuation?
}
```
