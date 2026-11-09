# AST and parsing

Parsing turns source text into a tree of its written forms. The lossless
syntax tree (AST) retains names, punctuation, parentheses, comments and
whitespace, so that tools can reproduce the source and locate each
occurrence. Name resolution and type checking produce later intermediate
representations (IRs); parsing alone establishes neither the meaning of a
program nor the validity of a check.

## Lexing

The source grammar is specified in the language reference.
[Lexical structure](../Language/LexicalStructure.md) defines source text,
its tokens, trivia and rejected text, and [Syntax](../Language/Syntax.md)
the declarations and expressions that the parser accepts and their
abstract syntax trees. The lexer and the parser implement them.

r[parsing.lexer.agreement] spec::parsing::lexer_agreement
The lexer divides every source text into the pieces, with the kinds, that
`next_piece?` of [Lexical structure](../Language/LexicalStructure.md)
gives, a word being a keyword exactly when `keyword?` holds of it, and the
`fren2 pieces` examples of that chapter are its pieces.

```fren
pub mod spec
pub mod spec::parsing

use spec::lexical

pub proc lexer_agreement(): (holds?) { ensure output: holds? }

tested lexer_agreement: "src/FrenTest/SpecChapters/Syntax.lean"
```

r[parsing.lexer.keywords] spec::parsing::reserved::rule
The lexer's table of keywords is `KEYWORDS`.

```fren
pub proc reserved(word: String): (keyword?) { ensure rule: keyword? iff lexical::keyword?(word) }
```

r[parsing.lexer.decoding] spec::parsing::decoding
Byte ingestion accepts exactly the byte sequences that are valid UTF-8, as
`lexical.source.encoding` defines source text, with the characters that
they encode.

```fren
pub proc decoding(): (holds?) { ensure output: holds? }

tested decoding: "src/FrenTest/SpecChapters/Syntax.lean"
```

r[parsing.lexer.numerals] spec::parsing::numerals
The parser gives a numeral the value that `lexical.numeral.value` defines,
beyond any fixed width.

```fren
pub proc numerals(): (holds?) { ensure output: holds? }

tested numerals: "src/FrenTest/SpecChapters/Syntax.lean"
```

## Parsing

The parser accepts the grammar's texts and builds their trees.

r[parsing.grammar.acceptance] spec::parsing::grammar_acceptance
The shared parser accepts exactly the texts that the grammar of
[Syntax](../Language/Syntax.md) accepts, independently of name resolution,
typing and solver verdicts.

```fren
pub proc grammar_acceptance(): (holds?) { ensure output: holds? }

tested grammar_acceptance: "src/FrenTest/SpecChapters/Syntax.lean"
```

r[parsing.grammar.trees] spec::parsing::expression_trees
The parser's tree of an accepted expression, without parentheses and
trivia, is the abstract syntax tree that `syntax.tree.productions` gives,
with its written grouping and order.

```fren
pub proc expression_trees(): (holds?) { ensure output: holds? }

tested expression_trees: "src/FrenTest/SpecChapters/Syntax.lean"
```

r[parsing.grammar.declaration-trees] spec::parsing::declaration_trees
The parser's tree of an accepted file, without parentheses and trivia, is
the sequence of declaration trees that `syntax.tree.productions` gives.

```fren
pub proc declaration_trees(): (holds?) { ensure output: holds? }

tested declaration_trees: "src/FrenTest/SpecChapters/Syntax.lean"
```

r[parsing.grammar.operators] spec::parsing::operators
The parser reads each operator's spelling as `unary_spelling` and
`binary_spelling` say, and orders the binary operators' precedences as
the categories of `syntax.property.print-parse` rank them.

```fren
pub proc operators(): (holds?) { ensure output: holds? }

tested operators: "src/FrenTest/SpecChapters/Syntax.lean"
```

## One parser and its entries

Each driver hands Fren text to the same parser, with an entry category.

r[parsing.shared.entry] spec::parsing::shared_entry
The file and context categories are one parser: for the same text and file
identity, they give the same tree or the same diagnostic. Which texts each
category accepts is `syntax.file.syntax`.

```fren
pub proc shared_entry(): (holds?) { ensure output: holds? }

tested shared_entry: "src/FrenParseTests/Adapter.lean"
```

r[parsing.shared.drivers] spec::parsing::shared_drivers
Every driver of Fren 2 text, the command line and the hosted reader of
Markdown blocks, calls this parser, and given identical Fren text, entry
category and file identity obtains the same tree or the same diagnostic,
before host positions are translated. Extraction from a host document is
separate from parsing: delimiters of the host are not Fren tokens.

```fren
pub proc shared_drivers(): (holds?) { ensure output: holds? }

trusted shared_drivers: "open: the command line and the hosted reader do not call the parser yet"
```

## Source ownership and locations

The lossless tree owns each byte of its source exactly once.

r[parsing.lossless.ownership] spec::parsing::ownership
The parse result retains the immutable source and an ordered partition of
its bytes into the pieces of `lexical.piece.division`, as nonempty token,
trivia or rejected-text slices, with no gaps or duplicated ownership,
including leading and trailing trivia.

```fren
pub proc ownership(): (holds?) { ensure output: holds? }

tested ownership: "src/FrenParseTests/Adapter.lean"
```

r[parsing.tree.structure] spec::parsing::tree_structure
The AST exposes structured declarations, expressions and their ordered
children, with written names and a token reference for each occurrence:
its terminals, in order, are exactly the lexer's tokens.

```fren
pub proc tree_structure(): (holds?) { ensure output: holds? }

tested tree_structure: "src/FrenParseTests/Adapter.lean"
```

r[parsing.source.bounds] spec::parsing::bounds
Every slice and diagnostic span has the source file identity and ordered
half-open UTF-8 byte offsets within that source's byte length.

```fren
pub proc bounds(): (holds?) { ensure output: holds? }

tested bounds: "src/FrenParseTests/Adapter.lean"
```

r[parsing.source.utf8] spec::parsing::boundaries
The parser reads source text as `lexical.source.encoding` defines it,
which also rejects invalid bytes before any tree is built. Token, trivia
and diagnostic endpoints lie on character boundaries, with the end of input
at the byte length.

```fren
pub proc boundaries(): (holds?) { ensure output: holds? }

tested boundaries: "src/FrenParseTests/Adapter.lean"
```

> **Note:** Tree nodes may reference or enclose slices, so the span of a
> node may overlap its children's spans without owning their bytes a
> second time. Two uses of `base` are separate occurrences even when later
> IRs share structure. These rules fix no constructors or storage layout.
> For `aéz`, the UTF-8 byte length is 4 and `é` occupies `[1, 3)`; `[2, 2)`
> is within bounds but inside `é`, so bounds alone do not make a character
> boundary.

## Complete input and failure

A parse result distinguishes success from failure.

r[parsing.complete] spec::parsing::complete_input
Success accounts for every input byte and contains a complete tree of the
selected entry category, with no missing or rejected syntax.

```fren
pub proc complete_input(): (holds?) { ensure output: holds? }

tested complete_input: "src/FrenParseTests/Adapter.lean"
```

r[parsing.failure] spec::parsing::failure
Malformed input, including truncated input such as `pub fn f(` or
`let x :=`, and input of trivia alone for the expression category, gives a
failure with a diagnostic: no exception, no silently dropped token, no
invented token and no success on a proper prefix of the input. A failure
keeps every byte of the input, and is never passed on as a complete tree.

```fren
pub proc failure(): (holds?) { ensure output: holds? }

tested failure: "src/FrenParseTests/Adapter.lean"
```

> **Note:** The parser is a total function of the text, the entry category
> and the file identity: for fixed arguments, parsing terminates with one
> result, tree and diagnostic. No rule states this, since the language of
> the implementation gives it.

r[parsing.diagnostic.anchor] spec::parsing::diagnostic_anchor
A syntax diagnostic is at a token, rejected text or the end of input, with
the empty span `[size, size)` there, and says what was expected.

```fren
pub proc diagnostic_anchor(): (holds?) { ensure output: holds? }

tested diagnostic_anchor: "src/FrenParseTests/Adapter.lean"
```

r[parsing.diagnostic.first] spec::parsing::diagnostic_first
A syntax diagnostic is at the first token, rejected text or end of input
where the grammar cannot continue, and what it says was expected is what
the grammar would accept there. A missing `}`, or an arm that ends at
`=>`, is reported at the end of input; an extra `}` after a valid
declaration, at that `}`; and rejected text, at its bytes.

```fren
pub proc diagnostic_first(): (holds?) { ensure output: holds? }

trusted diagnostic_first: "open: tests check the diagnostics of chosen texts, not that each is at the first point where the grammar cannot continue"
```

## Reconstruction

Emission reconstructs the source from the lossless tree.

r[parsing.roundtrip] spec::parsing::reconstruction
Emitting a successful parse reproduces the original bytes, and parsing
those bytes again, with the same entry category and file identity, gives
the same tree, token spellings and trivia.

```fren
pub proc reconstruction(): (holds?) { ensure output: holds? }

tested reconstruction: "src/FrenParseTests/Adapter.lean"
```

> **Note:** Emission is reconstruction, not formatting or serialization of
> an IR. A failure also reconstructs its input, but is not a successful
> parse. The text of an abstract syntax tree is `syntax.property.print-parse`.
> Resolution later replaces written names with item identities and de
> Bruijn indices using the [binding contracts](Bindings.md); those
> references do not replace written names in the AST.

## Byte classification

Two byte classes let the lexer and the boundary checks work on bytes.

r[parsing.primitive.space] spec::parsing::space_case::classification
A byte is whitespace exactly when it encodes a character of
`spec::lexical::WHITESPACE`: space, tab, LF or CR.

```fren
pub proc space_case(byte: Nat): (space?) {
    require byte_bound: byte < 256
    ensure classification: space? iff byte is 32 | 9 | 10 | 13
}
```

r[parsing.primitive.continuation] spec::parsing::continuation_case::classification
A UTF-8 continuation byte is in the inclusive interval 128 through 191.

```fren
pub proc continuation_case(byte: Nat): (continuation?) {
    require byte_bound: byte < 256
    ensure classification: continuation? iff 128 <= byte < 192
}
```

r[parsing.primitive.boundary] spec::parsing::boundary
In valid UTF-8, an offset inside the text is a character boundary exactly
when its byte is not a continuation byte; 0 and the byte length are
boundaries too.

```fren
pub proc boundary(): (holds?) { ensure output: holds? }

trusted boundary: "open: no theorem relates character boundaries to continuation bytes"
```
