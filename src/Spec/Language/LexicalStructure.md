# Lexical structure

A Fren source text is divided, from left to right, into *lexical
elements*: whitespace, comments, words, numerals and punctuators. Words,
numerals and punctuators are *tokens*, which the [grammar](Syntax.md)
reads. Whitespace and comments are *trivia*, which it skips. Text that
starts no lexical element is *rejected text*, and a source text that
contains any is not a Fren program.

Each rule's `status:` line says how it is established: `definition` for a
rule that only defines its terms, `smt` for a rule whose Fren block the
checker proves, `lean` for a Lean theorem of the chapter's wrapper, and
`tested` for an executable check of the wrapper that compares the actual
lexer with the chapter's definitions.

## Source text

**Syntax**

r[lexical.source.characters]
status: tested Spec.Language.LexicalStructure.lexer_agrees
A source text is a sequence of Unicode characters, decoded from UTF-8 as
`parsing.source.utf8` requires. The lexical rules are stated over these
characters. Positions in a source text are UTF-8 byte offsets. Only an
ASCII character can start a lexical element; any other character is part
of a comment or is rejected text.

r[lexical.source.line-ending] spec::lexical::line_ending?
status: tested Spec.Language.LexicalStructure.lexer_agrees
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

## Lexical elements

**Syntax**

r[lexical.element.syntax]
status: definition
The lexical elements have these forms. A quoted string stands for its
characters, `..` for a range of characters, and the other notation is
that of the [grammar](Syntax.md#notation).

```text
LexicalElement    ::= Whitespace | Comment | Word | Numeral | Punctuator
Whitespace        ::= U+0020 | U+0009 | U+000A | U+000D
Comment           ::= "--" CommentCharacter*
CommentCharacter  ::= any character but LF, and but a CR that an LF follows
Word              ::= WordStart WordCharacter* "?"?
WordStart         ::= "A".."Z" | "a".."z" | "_"
WordCharacter     ::= WordStart | Digit
Numeral           ::= Digit+
Digit             ::= "0".."9"
Punctuator        ::= "(" | ")" | "{" | "}" | "," | ":" | "+" | "-" | "*"
                    | "=" | "<" | ">" | "<=" | ">=" | "!=" | ":=" | "=>" | "::"
```

r[lexical.element.partition]
status: tested Spec.Language.LexicalStructure.lexer_agrees
Lexing divides the whole source text into consecutive, nonempty pieces,
each a lexical element or rejected text, with no gaps and no overlaps. The
pieces, in order, spell the source text exactly.

r[lexical.element.class] spec::lexical::element_class
status: tested Spec.Language.LexicalStructure.lexer_agrees
The class of the piece that starts at a position is decided by the first
one or two characters there, in this order: a whitespace character starts
whitespace; `--` starts a comment; a letter or `_` starts a word; a digit
starts a numeral; `<-` starts rejected text; a punctuator's first one or
two characters start a punctuator; and any other character starts
rejected text.

r[lexical.element.longest] spec::lexical::element_ends?
status: tested Spec.Language.LexicalStructure.lexer_agrees
A piece is the shortest nonempty text from its start after which
`element_ends?` holds of its class. For words, numerals, comments and
punctuators this is the longest text of that class, the rule of *maximal
munch*: `next_step` is one word, `<=` one punctuator and `123` one
numeral.

r[lexical.element.rejected]
status: tested Spec.Language.LexicalStructure.lexer_agrees
Rejected text is a single character that starts no lexical element, such
as `/`, `!`, `?`, `.`, `;` or a character outside ASCII, or the two
characters `<-`, which are rejected together, so that `x<-1` does not read
as `x < -1`. No parse of a source text that contains rejected text
succeeds (`parsing.complete`).

```fren
pub enum Class { Whitespace, Comment, Word, Numeral, Punctuator, Rejected }

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

pub fn element_class(remaining: String): Class :=
    if remaining.at(0) in WHITESPACE then Class::Whitespace
    else if remaining.starts_with?("--") then Class::Comment
    else if remaining.at(0).matches?(r"[A-Za-z_]") then Class::Word
    else if remaining.at(0).matches?(r"[0-9]") then Class::Numeral
    else if remaining.starts_with?("<-") then Class::Rejected
    else if remaining.slice(0, 2) in PUNCTUATORS or remaining.at(0) in PUNCTUATORS then Class::Punctuator
    else Class::Rejected

-- Whether a piece of class `kind` whose text so far is `lexeme` ends
-- before `remaining`, the source text after it. The `++` puts one character
-- after a punctuator, outside the decidable core; the wrapper compares this
-- function with the lexer on every short text instead.
set_option fren.lint.undecidable "allow" in
pub fn element_ends?(kind: Class, lexeme: String, remaining: String) := match kind {
    Class::Whitespace => true,
    Class::Comment => remaining = "" or line_ending?(remaining),
    Class::Word => lexeme.ends_with?("?") or not remaining.at(0).matches?(r"[A-Za-z0-9_?]"),
    Class::Numeral => not remaining.at(0).matches?(r"[0-9]"),
    Class::Punctuator => lexeme.len = 2 or not (lexeme ++ remaining.at(0)) in PUNCTUATORS,
    Class::Rejected => not (lexeme = "<" and remaining.starts_with?("-")),
}
```

r[lexical.trivia]
status: definition
Whitespace and comments are trivia. Trivia may come before the first
token, after the last, and between any two tokens, and the grammar does
not read it. The grammar depends on trivia only where the
[Syntax](Syntax.md) chapter says so: a `(` that must touch the name
before it, and a `mod` after a line ending.

**Examples**

```text
f(x)<=-1 -- note
```

The pieces of this line are the word `f`, the punctuator `(`, the word
`x`, the punctuators `)`, `<=` and `-`, the numeral `1`, a space, and the
comment `-- note`. In `x<-1` the pieces are `x`, the rejected text `<-`
and `1`.

## Comments

**Syntax**

r[lexical.comment.extent]
status: tested Spec.Language.LexicalStructure.lexer_agrees
`--` starts a comment, which runs up to the next line ending, not
including it, or to the end of the source text. A comment may contain any
character. There are no block comments: `/-` is the rejected text `/`
then the punctuator `-`. Since `--` always starts a comment, `x--1` is the
word `x` then a comment.

## Words, identifiers and keywords

**Syntax**

r[lexical.word.shape]
status: tested Spec.Language.LexicalStructure.lexer_agrees
A word is an ASCII letter or `_`, then any number of ASCII letters, digits
and `_`, then at most one `?`, which ends it. `_` alone is a word. In
`a?b` the word `a?` ends at its `?`, and `b` is a second word.

**Legality rules**

r[lexical.keyword.set] spec::lexical::keyword?
status: tested Spec.Language.LexicalStructure.keywords_agree
A word is a *keyword* if it is one of `KEYWORDS`, and an *identifier*
otherwise. No word is both. A keyword is never an identifier, even where
the grammar has no construct that uses it.

r[lexical.keyword.shape] spec::lexical::keyword_shape::{lowercase, grammar, contextual}
status: smt
Every keyword is lowercase ASCII letters, so it is a word, and none ends
in `?`: `if?` and `match?` are identifiers. The keywords that the grammar
uses, `GRAMMAR_KEYWORDS`, are keywords. The *contextual words*,
`CONTEXTUAL`, are identifiers, not keywords, which the grammar gives a
meaning at certain positions (see
[Syntax](Syntax.md#names-and-paths)).

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
}

pub const GRAMMAR_KEYWORDS: Set<String> := {
    "mod",
    "pub",
    "enum",
    "fn",
    "expect",
    "iff",
    "and",
    "or",
    "div",
    "in",
    "if",
    "then",
    "else",
    "match",
    "let",
}

pub const CONTEXTUAL: Set<String> := {"assume", "not", "true", "false", "Bool", "Int"}

pub fn keyword?(word: String) := word in KEYWORDS

expect keyword_shape(word: String) {
    expect lowercase: when keyword?(word), word.matches?(r"[a-z]+")
    expect grammar: when word in GRAMMAR_KEYWORDS, keyword?(word)
    expect contextual: when word in CONTEXTUAL, word.matches?(r"[A-Za-z]+") and not keyword?(word)
}
```

## Numerals

**Syntax**

r[lexical.numeral.value]
status: tested Spec.Language.LexicalStructure.numerals_agree
A numeral is a run of ASCII digits as long as possible, and denotes the
natural number that it writes in decimal, without bound. Leading zeros
are allowed: `007` denotes 7. A numeral has no sign, base prefix, digit
separator, fraction or exponent: a negative number is written with unary
minus, `0x1F` is the numeral `0` then the word `x1F`, and `1.5` is the
numeral `1`, the rejected text `.` and the numeral `5`.

## Punctuators

**Syntax**

r[lexical.punctuator.longest]
status: tested Spec.Language.LexicalStructure.lexer_agrees
A punctuator is one of `PUNCTUATORS`, and is two characters where its
first two characters are one: `a<=b` has the punctuator `<=`, and `::=` is
`::` then `=`. `!` is a punctuator only as the first character of `!=`;
alone it is rejected text. `--` starts a comment, and `<-` is rejected
text, not two punctuators.

**Legality rules**

r[lexical.punctuator.shape] spec::lexical::punctuator_shape
status: smt
Every punctuator is one or two characters, and neither `--` nor `<-` is
one.

```fren
expect punctuator_shape(text: String) {
    expect length: when text in PUNCTUATORS, text.len is 1 | 2 and not text is "--" | "<-"
}
```
