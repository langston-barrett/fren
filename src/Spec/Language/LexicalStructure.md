# Lexical structure

Lexing divides a Fren source text, from left to right, into pieces:
whitespace, comments, words, numerals, punctuators and rejected text. The
[grammar](Syntax.md) reads the words, numerals and punctuators, and skips
whitespace and comments.

That the lexer divides a text as this chapter says is a requirement of
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

r[lexical.class.definition] spec::lexical::{Class, WHITESPACE, PUNCTUATORS, in_class?}
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

r[lexical.piece.longest] spec::lexical::{classed?, longest?}
From each position of a source text, lexing reads the longest text there
that belongs to a lexical class, the rule of *maximal munch*: `next_step`
is one word, `<=` one punctuator, `123` one numeral and `--` a comment
rather than two punctuators. `longest?` decides whether that text has `n`
characters: the first `n` characters at the position belong to a class,
and the first `n + 1` do not.

```fren
-- Whether `text` belongs to a lexical class.
pub fn classed?(text: String) := exists (kind: Class), in_class?(kind, text)

-- Whether the longest text of a class that starts `remaining`, the source
-- text from a position to its end, has `n` characters.
set_option fren.lint.undecidable "allow" in  -- a slice at a position that is not a constant
pub fn longest?(remaining: String, n: Int) :=
    0 < n <= remaining.len and classed?(remaining.slice(0, n))
    and (n = remaining.len or not classed?(remaining.slice(0, n + 1)))
```

r[lexical.piece.shorter] spec::lexical::shorter::{whitespace, comment, word, numeral, punctuator}
A text of a class, less its last character, is a text of a class too,
unless it is empty or the `!` of `!=`: a comment gives a comment or `-`, a
word a word that the pattern shows to have no `?`, a numeral a numeral, and a punctuator a
punctuator or that `!`. So looking one character further finds the longest
text, and a position where no text of one or two characters belongs to a
class starts no text of a class at all.

```fren
set_option fren.lint.undecidable "allow" in  -- a concatenation with a text that is not a constant
expect shorter(text: String, last: String) {
    assume character: last.len = 1
    assume longer: text != ""

    expect whitespace: not in_class?(Class::Whitespace, text ++ last)
    expect comment: when in_class?(Class::Comment, text ++ last), in_class?(Class::Comment, text) or text = "-"
    expect word: when in_class?(Class::Word, text ++ last), text.matches?(r"[A-Za-z_][A-Za-z0-9_]*")
    expect numeral: when in_class?(Class::Numeral, text ++ last), in_class?(Class::Numeral, text)
    expect punctuator: when in_class?(Class::Punctuator, text ++ last),
        in_class?(Class::Punctuator, text) or text ++ last = "!="
}
```

r[lexical.piece.next] spec::lexical::next_piece?
`next_piece?` decides the *next piece* at a position, its class and its
number of characters `n`. It is the longest text of a class there, with
that class, but in three cases:

- where `<-` starts, the piece is those two characters, and is *rejected
  text*, of no class;
- where no text of a class starts, the piece is the next character alone,
  and is rejected text too;
- a comment ends before a line ending: when the longest comment ends with
  a CR that an LF follows, the piece is that comment without the CR, which
  is whitespace.

```fren
set_option fren.lint.undecidable "allow" in  -- slices at positions that are not constants
pub fn next_piece?(remaining: String, kind: Option<Class>, n: Int) :=
    0 < n <= remaining.len
    and (if remaining.starts_with?("<-") then kind = Option::None and n = 2
        else if not classed?(remaining.at(0)) and not classed?(remaining.slice(0, 2)) then
        kind = Option::None and n = 1
        else match kind {
            Option::None => false,
            Option::Some(Class::Comment) => in_class?(Class::Comment, remaining.slice(0, n))
                and (if remaining.slice(n, 2) = "\r\n" then longest?(remaining, n + 1)
                else longest?(remaining, n) and remaining.slice(n - 1, 2) != "\r\n"),
            Option::Some(other) =>
                in_class?(other, remaining.slice(0, n)) and longest?(remaining, n),
        })
```

r[lexical.piece.comment-end]
A comment never includes the CR of a line ending: `-- a` and then CR and
LF is the comment `-- a`, the whitespace CR and the whitespace LF.

r[lexical.piece.rejected]
Rejected text is `<-` at a position, or a single character that starts no
text of a class there: for example `/`, `.`, `;`, `"`, `[`, `#`, a `!`
that no `=` follows, a `?` that does not end a word, as the second of
`a??`, a control character such as a form feed, a byte order mark, and
any other character outside ASCII outside a comment. Inside a comment
nothing is rejected: `-- a <- b` is one comment. A source text that
contains rejected text is no program.

> **Rationale:** `<-` is reserved for a possible future operator, and is
> a Lean token, which today's Fren, read by Lean, cannot accept as `<`
> then `-`. Rejecting it as one piece keeps `x<-1` from meaning `x < -1`,
> which a future `<-` would change; write `x < -1`. This is decision L1 in
> the [development coverage](../../../docs/fren2-specification-coverage.md#syntax-decisions-and-design-debt).

r[lexical.piece.determined] spec::lexical::pieces::{within, of_class, determined}
A next piece is not empty and ends within the text. A piece of a class is
a text of that class, and a piece's length determines its class, or that it
is rejected text.

```fren
set_option fren.lint.undecidable "allow" in  -- slices at positions that are not constants
expect pieces(remaining: String, kind: Class, a: Option<Class>, b: Option<Class>, n: Int) {
    expect within: when next_piece?(remaining, a, n), 0 < n <= remaining.len
    expect of_class: when next_piece?(remaining, Option::Some(kind), n), in_class?(kind, remaining.slice(0, n))
    expect determined: when next_piece?(remaining, a, n) and next_piece?(remaining, b, n), a = b
}
```

r[lexical.piece.division] spec::lexical::division
The *pieces* of a source text are its next piece at position 0, then the
next piece where each piece ends, to the end of the text. Every text has
exactly one such division: each position before the end has one next
piece, which is not empty and ends within the text, so the pieces are
consecutive, with no gaps and no overlaps, and spell the text exactly.
No text of a class that starts where a piece starts is longer than the
piece, but a comment up to the CR of a line ending.

```fren
pub proc division(): (holds?) { ensure output: holds? }

tested division: "src/FrenTest/SpecChapters/Syntax.lean"
```

r[lexical.class.disjoint] spec::lexical::classes::disjoint
No text belongs to two classes: the class of each piece is determined.

```fren
expect classes(a: Class, b: Class, text: String) {
    expect disjoint: when a != b and in_class?(a, text), not in_class?(b, text)
}
```

### Examples

Each block gives a text on its first line, where `\r` writes a CR and `\n`
an LF, and then its pieces, one a line: the piece's kind and its text, with
each character of whitespace written by its code point, as `U+0020`. A
word's kind is `keyword` or `identifier`, which
[Words, identifiers and keywords](#words-identifiers-and-keywords) tells
apart.

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

```fren2 pieces
a??
identifier a?
rejected ?
```

There are no string literals: a quote is rejected text.

```fren2 pieces
"a"
rejected "
identifier a
rejected "
```

Each character of whitespace is a piece of its own, and a comment stops
before a line ending.

```fren2 pieces
a  -- b <- c\r\n
identifier a
whitespace U+0020
whitespace U+0020
comment -- b <- c
whitespace U+000D
whitespace U+000A
```

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
> keeps its meaning when those constructs arrive. Today's Fren reserves
> each of them but `true`, `false` and `not`, and Lean's keywords besides
> (`lang::RESERVED`). This is decision L2 in the
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
