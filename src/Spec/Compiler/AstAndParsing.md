# AST and parsing

Parsing turns source text into a tree of its written forms. The abstract
syntax tree (AST) retains names, punctuation, comments and whitespace so
that tools can reproduce the source and locate each occurrence. Name
resolution and type checking produce later intermediate representations
(IRs); parsing alone establishes neither meaning nor validity of a check.

## Walking subset

The initial parser supports modules, public declarations, payload-free
enumerations, non-recursive expression-bodied functions, and global
expectations with typed parameters and labelled `assume` and `expect`
members. Types are `Bool`, `Int` and named enumerations. Expressions include
names and qualified paths, Boolean and decimal integer literals, calls,
parentheses, `if`, `let` and enumeration `match`. The operator slice is
unary `-`; binary `+`, `-`, `*`, `div`, `mod`, `=`, `!=`, `<`, `<=`, `>`, `>=`;
`not`, `and`, `or` and `iff`. Parsing an operator does not establish its
operand types or definedness.

For example, these declarations exercise ordered variants, match arms,
argument lists, nested calls and labelled checks:

```fren
pub mod walking

pub enum Light { Red, Amber, Green }

pub fn next(l: Light): Light := match l {
    Light::Red => Light::Green,
    Light::Green => Light::Amber,
    Light::Amber => Light::Red,
}

pub fn wait(l: Light, base: Int): Int := match l {
    Light::Red => base + 30,
    Light::Amber => base + 5,
    Light::Green => base,
}

expect cycles(l: Light) { expect back: next(next(next(l))) = l }

expect waits(l: Light, base: Int) {
    assume bounded: base <= 100
    expect at_most: wait(l, base) <= 130
}

pub fn choose(b?, base: Int): Int := let delay := base + 5 in if b? then delay else base

expect division(x: Int) { expect euclidean: x = (x div 2) * 2 + x mod 2 }
```

Integer division is written `div`; `/` is rejected. The division example
uses the constant nonzero divisor 2. The remainder operator `mod` must be
on the line where its left operand ends. A `mod` after an LF or CRLF starts
a module declaration instead, including when comments intervene. Within an
expression entry or an unclosed delimiter, that declaration is unexpected.
A remainder may put its right operand on the next line.

`base + 5 * 2` groups as `base + (5 * 2)`, and `base - 5 - 2` as
`(base - 5) - 2`. Calls bind before arithmetic; unary minus binds before
multiplication, then addition, then comparisons, then `not`, `and`, `or`
and `iff`, in decreasing precedence. Parentheses override that grouping.
A prefix operand must respect this precedence too: `a + not b` and `-not b`
require parentheses around the `not` expression. A `let` used as an
operator's operand likewise requires parentheses, as in
`a and (let x := true in x)`. Repeated `not not b` is valid. `if` and `match`
are atoms and do not acquire these restrictions.
`iff` does not associate: write `(a iff b) iff c` or `a iff (b iff c)`.
This walking slice has binary comparisons only. Unparenthesized comparison
chains, including the full language's `a < b <= c`, are unsupported rather
than parsed as nested binary operators. Explicitly parenthesized comparisons
remain syntax trees whose operand types are checked later.
A `let` has the form `let x := value in body`; its body extends to the
right. The definition's value is read at the `iff` level, so a nested `let`
there requires parentheses; a right-nested `let` in the body remains valid.
An `if` requires both `then` and `else`. A match scrutinee is an atom, such
as a name, call, parenthesized expression, `if` or nested `match`; a bare
operator or `let` expression there requires parentheses. A match arm pairs
a qualified variant pattern with an expression at the `iff` level using
`=>`, so a bare `let` arm body also requires parentheses. Arms are
comma-separated and may have a trailing comma. Function parameters use
`name: Type` (a `?` suffix supplies `Bool` when the annotation is omitted),
and a function body follows `:=`. A suffix does not remove an explicit
annotation: `b?: Bool` and `b?: Int` both parse, and the latter's type
inconsistency is checked later. Named type paths are read in full before a
bare `Bool` or `Int` is classified as built-in: `Int::T` and `Bool::T` are
written paths whose resolution is also later work.
Calls apply a written path, as in `f(x)` or `A::f(x)`, rather than an
arbitrary expression or a previous call result. The opening `(` touches
the last name: spaces, tabs, line endings and comments are not allowed
between them. Function and global-expectation parameter lists likewise
begin immediately after the declaration name. Ordinary grouping
parentheses may still follow trivia. These are syntax rules; a named
application such as `unknown(x)` or `x(y)` still parses before resolution
or typing.
Function parameter lists and ordinary call argument lists are nonempty and
do not allow a trailing comma. An enumeration has at least one variant;
its variants may have a trailing comma. Global-expectation parameters may
be empty and may have a trailing comma. Match arms may have a trailing
comma or be empty; missing-variant checking, including an empty match,
remains a later pass. Empty declaration sequences and empty expectation
member blocks are also syntax.

**Proof obligations**

r[parsing.walking.forms]
The shared parser recognizes these forms with their written grouping and
order, independently of name resolution, typing and solver verdicts.

Thus `y + 1` is a syntactically valid body even when `y` is unbound, and
`l + 1` parses even when `l` later has type `Light`. Their static errors
belong to resolution and typing. Likewise the expectation
`expect never_red: next(l) != Light::Red` parses successfully; its false
claim is discovered after parsing. A match with missing variants is also
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

A *token* is a written identifier, keyword, literal or punctuator. *Trivia*
is text between tokens: spaces, tabs, line endings and comments. The
walking identifiers start with an ASCII letter or `_`, followed by ASCII
letters, digits or `_`, with an optional final `?`. Fren's reserved words
remain reserved even when their constructs are unsupported: `proc` and
`forall` are not names in this slice. Contextual `assume` is an ordinary
name outside an expectation member's keyword position. `Bool`, `Int`,
`true`, `false` and `not` are interpreted at their type, literal or operator
positions, rather than globally reserved from name positions. This does not
add the constructs or broader lexical forms deferred below. The walking
slice includes `--` line comments ending before LF or CRLF, or
at EOF. LF and CRLF retain their original bytes. A keyword is recognized only
at a token boundary: `next_step` is one identifier. Punctuators use longest
matching spelling, so `<=`, `!=`, `:=`, `=>` and `::` are not split into
shorter tokens. The unsupported punctuator `<-` is likewise one rejected
slice; `x<-1` fails, while `x < -1` contains a comparison and unary minus.
Comment text is not parsed as declarations.

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

The walking parser consumes decoded text. Invalid bytes are an ingestion
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

This slice requires a primary diagnostic; additional recovery diagnostics
are optional but deterministic and in source order. Missing `}` or an arm
ending at `=>` reports EOF with the empty span `[size, size)`. An extra `}`
after a valid declaration reports that token. `pub fn f(` and an incomplete
`let x :=` fail rather than inventing a body. An unrecognized character is
retained as rejected text and diagnosed at its byte span. These malformed
and truncated inputs must be supported as failures, including comment-only
expression input. Recovery nodes, if provided, explicitly distinguish missing
syntax from written tokens and own no invented bytes. Incremental parsing,
editor completion and useful recovery trees are future extensions, not
requirements to implement a second tolerant parser now.

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

## Checked byte primitives and remaining evidence

These contracts classify raw byte values. They neither implement a lexer
nor accept a caller-supplied parse verdict. The continuation-byte interval
is useful only after UTF-8 validation: an internal offset in valid UTF-8
text is a character boundary exactly when its byte is not a continuation
byte. Zero and EOF are boundaries independently. This table alone cannot
validate an encoding or connect a byte to a particular source offset.

**Dynamic semantics**

r[parsing.primitive.space] spec::parsing::space_case::{classification, space, tab, lf, cr, ordinary}
The walking slice's ASCII whitespace bytes are space, tab, LF and CR.

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

The chapter wrapper checks these primitives and the successful walking
example. The parser, AST and shared typed-context adapter are not implemented
by this chapter. The rules labelled **Proof obligations** remain requirements,
not discharged theorems about an empty library or assumed parser.

- [ ] State the complete-input, ownership, boundary, determinism and roundtrip
  laws in Lean over the actual `FrenParse`/`FrenAst` APIs, or bind uninterpreted
  Fren laws to them with genuine `impl` proofs where expressible.
- [ ] Bind the actual byte classifiers to the primitive meanings above; reuse
  the existing Span bounds/translation laws rather than duplicating them.
- [ ] Exercise the actual parser directly with Plausible and textual tests:
  successful, ill-typed-but-parsable, malformed and truncated text; Unicode
  comments, empty input, trailing junk, EOF and alternate trivia. Report
  accepted/rejected grammar premises and test deliberately perturbed bounds,
  byte classification and grouping. Sampled properties are not proofs.
- [ ] Check driver and typed-context adapter agreement on the same extracted
  text, preserving source-map and callback-input bytes.

Full-language syntax, payload patterns, generics, closures, procedures,
interfaces, views, broader lexical forms and editor recovery require later
chapter extensions before their implementation. This walking slice supplies
no recursive Fren parser model, no semantic pass implementation and no
prerequisite to extend Fren's recursive specification features.
