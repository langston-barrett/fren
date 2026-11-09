# Lexical structure

Lexing divides a Fren source text, from left to right, into pieces:
whitespace, comments, words, numerals, punctuators and rejected text. The
[grammar](Syntax.md) reads the words, numerals and punctuators, and skips
whitespace and comments.

The rules define lexing; their properties are Fren expectations that the
checker proves. That the actual lexer lexes as they say is a requirement of
[AST and parsing](../Compiler/AstAndParsing.md#lexing).

## Source text

A source text is what a Fren file or a Fren block of a host document
contains.

r[lexical.source.encoding]
A source text is a sequence of bytes that is valid UTF-8, read as the
sequence of Unicode characters that it encodes. Bytes that are not valid
UTF-8 are no source text: they are rejected before lexing, and no
character replaces them. Positions in a source text are byte offsets into
its UTF-8 encoding, and a position is never inside a character.

r[lexical.source.line-ending] spec::lexical::line_ending?
A *line ending* is a line feed (LF, U+000A), or a carriage return (CR,
U+000D) immediately followed by a line feed. A CR that no LF follows is
whitespace, but ends no line.

```fren
pub mod spec
pub mod spec::lexical

-- `remaining` is the source text from a position to its end.
pub fn line_ending?(remaining: String) :=
    remaining.starts_with?("\n") or remaining.starts_with?("\r\n")
```

## Lexical classes

Each piece that lexing produces, but rejected text, belongs to one class.

r[lexical.class.definition] spec::lexical::in_class?
The *lexical classes* are whitespace, comments, words, numerals and
punctuators, and `in_class?` states which texts belong to each:

- *whitespace* is a single space, tab (U+0009), LF or CR;
- a *comment* is `--` and then any characters but LF;
- a *word* is an ASCII letter or `_`, then any number of ASCII letters,
  digits and `_`, then at most one `?`;
- a *numeral* is one or more ASCII digits;
- a *punctuator* is one of `PUNCTUATORS`.

Words, numerals and punctuators are *tokens*. Whitespace and comments are
*trivia*.

```fren
pub enum Class { Whitespace, Comment, Word, Numeral, Punctuator }

pub const WHITESPACE: Set<String> := {" ", "\t", "\n", "\r"}

pub const PUNCTUATORS: Set<String> := {
    "(",
    ")",
    "{",
    "}",
    ",",
    ":",
    "+",
    "-",
    "*",
    "%",
    "=",
    "<",
    ">",
    "<=",
    ">=",
    "!=",
    ":=",
    "=>",
    "::",
}

pub fn in_class?(kind: Class, text: String) := match kind {
    Class::Whitespace => text in WHITESPACE,
    -- Not a raw string: the pattern needs a line feed, which a raw string
    -- cannot write.
    Class::Comment => text.matches?("--[^\n]*"),
    Class::Word => text.matches?(r"[A-Za-z_][A-Za-z0-9_]*[?]?"),
    Class::Numeral => text.matches?(r"[0-9]+"),
    Class::Punctuator => text in PUNCTUATORS,
}
```

## Pieces

Lexing reads the longest text of some class at each position.

r[lexical.piece.longest]
Lexing divides the whole source text into consecutive, nonempty pieces,
with no gaps and no overlaps, which spell the source text exactly. From
each position, the next piece is the longest nonempty text there that
belongs to a lexical class, and it has that class, the rule of *maximal
munch*: `next_step` is one word, `<=` one punctuator, `123` one numeral
and `--` a comment rather than two punctuators. There are two exceptions,
stated next.

r[lexical.piece.comment-end]
A comment ends before a line ending: when the longest comment ends with a
CR that an LF follows, the comment does not include that CR, which is
whitespace.

r[lexical.piece.rejected]
Where `<-` starts, those two characters are one piece of *rejected text*.
Where no text of any class starts, the piece is the next character alone,
and is rejected text too: `/`, `!` without `=`, `?` after a non-word,
`.`, `;`, and any character outside ASCII outside a comment. A source text
that contains rejected text is no program.

> **Rationale:** `<-` is reserved for a possible future operator, and is
> a Lean token, which today's Fren, read by Lean, cannot accept as `<`
> then `-`. Rejecting it as one piece keeps `x<-1` from meaning `x < -1`,
> which a future `<-` would change; write `x < -1`. This is decision L1 in
> the [development coverage](../../../docs/fren2-specification-coverage.md#syntax-decisions-and-design-debt).

r[lexical.class.disjoint] spec::lexical::classes::{disjoint, punctuator_extension}
No text belongs to two classes: the class of each piece is determined.
A punctuator of two characters, other than `!=`, extends one of one
character.

```fren
expect classes(a: Class, b: Class, text: String) {
    expect disjoint: when a != b and in_class?(a, text), not in_class?(b, text)
    expect punctuator_extension: when text in PUNCTUATORS and text.len = 2 and text != "!=",
        text.at(0) in PUNCTUATORS
}
```

### Examples

Each block gives a text on its first line and then its pieces, one a line:
the piece's kind and its text, with a space written as `U+0020`.

```fren2 pieces
f(x)<=-1 -- note
identifier f
punctuator (
identifier x
punctuator )
punctuator <=
punctuator -
numeral 1
whitespace U+0020
comment -- note
```

```fren2 pieces
x<-1
identifier x
rejected <-
numeral 1
```

```fren2 pieces
x--1
identifier x
comment --1
```

```fren2 pieces
/-
rejected /
punctuator -
```

```fren2 pieces
if? true? not
identifier if?
whitespace U+0020
identifier true?
whitespace U+0020
keyword not
```

There are no block comments: `/-` is rejected text and a punctuator.

## Trivia

The grammar reads tokens; trivia separates them.

r[lexical.trivia]
Trivia may come before the first token, after the last, and between any
two tokens. The grammar does not read trivia, except where the
[Syntax](Syntax.md#notation) chapter says so: a `(` that must touch the
token before it.

## Words, identifiers and keywords

Words are the names of a program and its reserved words.

r[lexical.keyword.set] spec::lexical::{KEYWORDS, keyword?}
A word is a *keyword* if it is one of `KEYWORDS`, and an *identifier*
otherwise. A keyword is never an identifier, even where the grammar has no
construct that uses it. A word that ends in `?` is never a keyword: `if?`
and `true?` are identifiers. `true`, `false` and `not` are keywords: no
declaration, parameter, binder, label or path segment is named by one.

```fren
pub const KEYWORDS: Set<String> := {
    "mod",
    "use",
    "pub",
    "ordered",
    "enum",
    "struct",
    "type",
    "fn",
    "const",
    "proc",
    "trait",
    "expect",
    "impl",
    "interp",
    "tested",
    "trusted",
    "iff",
    "and",
    "or",
    "union",
    "inter",
    "minus",
    "subset",
    "join",
    "div",
    "is",
    "in",
    "if",
    "then",
    "else",
    "match",
    "forall",
    "exists",
    "with",
    "let",
    "where",
    "table",
    "true",
    "false",
    "not",
}

pub fn keyword?(word: String) := word in KEYWORDS
```

> **Rationale:** Most keywords name constructs of today's Fren that the
> grammar of [Syntax](Syntax.md) does not have yet, such as `struct`,
> `proc`, `forall` and `table`. They are reserved now so that a program
> keeps its meaning when those constructs arrive, and so that a text reads
> alike in both front ends, which today's Fren, which reserves the same
> words, requires. This is decision L2 in the
> [development coverage](../../../docs/fren2-specification-coverage.md#syntax-decisions-and-design-debt).

r[lexical.keyword.words] spec::lexical::keywords::words
Every keyword is a word of lowercase ASCII letters.

```fren
expect keywords(word: String) {
    expect words: when word in KEYWORDS, word.matches?(r"[a-z]+") and in_class?(Class::Word, word)
}
```

## Numerals

Numerals write natural numbers.

r[lexical.numeral.value]
A numeral denotes the natural number that it writes in decimal, without
bound. Leading zeros are allowed: `007` denotes 7. A numeral has no sign,
base prefix, digit separator, fraction or exponent: a negative number is
written with unary minus, `0x1F` is the numeral `0` then the word `x1F`,
and `1.5` is the numeral `1`, the rejected text `.` and the numeral `5`.
