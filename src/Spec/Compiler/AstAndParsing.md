# AST and parsing

Parsing turns source text into a tree of its written forms. The abstract
syntax tree (AST) retains names, punctuation, comments and whitespace so
that tools can reproduce the source and locate each occurrence. Name
resolution and type checking produce later intermediate representations
(IRs); parsing alone establishes neither meaning nor validity of a check.

## Source forms

The source grammar is specified in the language reference.
[Lexical structure](../Language/LexicalStructure.md) defines the tokens,
trivia and rejected text of a source text, and
[Syntax](../Language/Syntax.md) the declarations and expressions that the
parser accepts, with their grouping and order. This chapter states what
the parser's result contains and how it relates to the source text.

**Proof obligations**

r[parsing.walking.forms]
The shared parser recognizes the forms of [Syntax](../Language/Syntax.md)
with their written grouping and order, independently of name resolution,
typing and solver verdicts.

Thus `y + 1` is a syntactically valid body even when `y` is unbound, and
`l + 1` parses even when `l` later has type `Light`. Their static errors
belong to resolution and typing. A match with missing variants is also
a syntax tree whose exhaustiveness remains to be checked.

## One parser and its consumers

`FrenParse` owns the shared parser, and `FrenAst` owns its lossless tree
interface. The command-line driver supplies a source file. The hosted
driver supplies extracted Markdown blocks or a `fren { … }` body, with a
source map back to the containing document. Extraction is separate from
parsing: delimiters belonging to the host are not Fren tokens.

The textual test runner already accepts a typed context parser through
`Runner.of`. Its Fren adapter will parse declarations from the context
text once, then pass that typed AST context to the library callback. The
runner's case/result markers remain its container format. They do not
define another Fren grammar.

**Proof obligations**

r[parsing.shared.entry]
The drivers and the Fren textual-context adapter call the same parser;
given identical Fren text, entry category and file identity, they obtain
the same tree or parse diagnostic data before host-position translation.

A context is a sequence of declarations, not an expression or an opaque
string called an AST. Empty or comment-only context text denotes an empty
sequence. File parsing also accepts an empty declaration sequence.
Expression parsing, where offered for library tests, requires one expression.
Each entry consumes its complete input, allowing trailing trivia. Separate
entry categories select grammar roots, not independent parser implementations.

## Source ownership and locations

A *token* is a written word (an identifier or keyword), numeral or
punctuator. *Trivia* is text between tokens: whitespace and comments.
*Rejected text* starts no lexical element. [Lexical
structure](../Language/LexicalStructure.md) defines each of these, and how
the source text is divided into them. For example, `/` is rejected text: integer
division is written `div`.

**Proof obligations**

r[parsing.lossless.ownership]
The parse result retains the immutable source and an ordered partition of
its bytes into nonempty token, trivia or rejected-text slices, with no gaps
or duplicated ownership, including leading and trailing trivia.

r[parsing.tree.structure]
The AST exposes structured declarations, expressions and their ordered
children, with written names and token references for each occurrence.

r[parsing.source.bounds]
Every slice and diagnostic span has the source file identity and ordered
half-open UTF-8 byte offsets within that source's byte length.

Tree nodes may reference or enclose slices, so enclosing node spans may
overlap their children's spans. Those references do not own the bytes a
second time. Two uses of `base` have separate source occurrences even when
later IR nodes share structure. The tree may store trivia separately from
its grammar nodes; these contracts do not prescribe concrete constructors
or freeze a storage layout. Keeping a source string without structured
forms does not satisfy the AST contract.

The [base definitions](BaseDefinitions.md#files-spans-and-source-maps)
define spans and source maps. The existing `FrenSource.Span.checked` laws
already characterize `start ≤ stop ≤ size` for natural byte offsets and
preserve file identity and endpoints. Its `offset` laws cover translation
of an unchanged embedded body after the caller establishes extraction and
host bounds. Parsing must establish these premises from its actual source;
a size supplied independently of that source is insufficient.

For `aéz`, the UTF-8 byte length is 4 and `é` occupies `[1, 3)`.
`[2, 2)` is byte-bounded but lies inside `é`. Bounds checking alone does
not prove a character boundary.

**Proof obligations**

r[parsing.source.utf8]
For decoded UTF-8 text, token, trivia and parse-diagnostic endpoints lie on
character boundaries, with EOF at the byte length; ingestion rejects invalid
UTF-8 bytes before constructing the text AST, without replacement decoding.

The parser consumes decoded text. Invalid bytes are an ingestion
failure, not a successful parse. A diagnostic for invalid encoding may
identify the offending raw byte range. No editor column or UTF-16 offset
is substituted for a byte offset; conversion occurs at the editor boundary.

## Complete input, failure and partial text

A parse result distinguishes success from failure. Failure is ordinary data
and may retain a lossless partial tree for reporting or editing. It is
never passed to name resolution as a successful complete tree.

**Proof obligations**

r[parsing.complete]
Success accounts for every input byte and contains a complete tree of the
selected entry category, with no missing or rejected syntax.

r[parsing.failure]
Malformed or unsupported input returns failure with a diagnostic, without
exceptions, silent token deletion or success on a proper input prefix.

r[parsing.determinism]
For fixed text, entry category and file identity, parsing terminates with
the same success/failure result, tree contents and ordered diagnostic data.

r[parsing.diagnostic.anchor]
A syntax diagnostic identifies the first unexpected token, rejected character or EOF where
required syntax is missing, and describes the expected form.

This source grammar requires a primary diagnostic; additional recovery diagnostics
are optional but deterministic and in source order. Missing `}` or an arm
ending at `=>` reports EOF with the empty span `[size, size)`. An extra `}`
after a valid declaration reports that token. `pub fn f(` and an incomplete
`let x :=` fail rather than inventing a body. An unrecognized character is
retained as rejected text and diagnosed at its byte span. These malformed
and truncated inputs must be supported as failures, including comment-only
expression input. Recovery nodes, if provided, explicitly distinguish missing
syntax from written tokens and own no invented bytes. Incremental parsing,
editor completion and tolerant recovery trees are outside this input contract.

**Proof obligations**

r[parsing.roundtrip]
Emitting a successful lossless parse reproduces the original UTF-8 bytes;
reparsing those bytes under the same entry category and file identity reproduces the same
structured syntax, token spelling and trivia, ignoring allocation identity.

The Lean proposition `LosslessOnSuccess parse emit` states
`∀ source tree, parse source = .ok tree → emit tree = source`, with the
entry category and file identity fixed by the supplied functions. The wrapper
defines this obligation without asserting it or supplying a parser. It must
be instantiated with the actual shared parser and emitter.

Emission here means source reconstruction, not formatting or IR
serialization. Retaining rejected input also allows failure results to
reconstruct the input, but does not make a partial tree a successful parse.
An arbitrary generated AST needs a separate well-formedness premise for
printing/parsing; a raw source roundtrip proves no scope or type property.
Resolution later replaces source names with item identities and de Bruijn
indices using the [binding contracts](Bindings.md). Those semantic references
do not replace written names in the AST.

## Byte classification

These contracts classify raw byte values. They neither implement a lexer
nor accept a caller-supplied parse verdict. The continuation-byte interval
is useful only after UTF-8 validation: an internal offset in valid UTF-8
text is a character boundary exactly when its byte is not a continuation
byte. Zero and EOF are boundaries independently. This table alone cannot
validate an encoding or connect a byte to a particular source offset.

**Dynamic semantics**

r[parsing.primitive.space] spec::parsing::space_case::{classification, space, tab, lf, cr, ordinary}
The ASCII whitespace bytes are space, tab, LF and CR.

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
A UTF-8 continuation byte is in the inclusive interval 128 through 191.

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

Implementation correspondence and proof coverage are recorded in the
[development coverage document](../../../docs/fren2-specification-coverage.md).
