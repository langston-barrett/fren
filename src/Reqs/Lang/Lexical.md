# Lexical structure

Fren is lexed as Lean is, so that a spec can be part of a Lean file.

## Comments

`--` starts a comment that runs to the end of the line. `/-` and `-/`
delimit a block comment, and block comments nest.

## Identifiers

Identifiers are ASCII: a letter or `_`, then letters, digits, `_` and
`'`. An identifier may end in `?`, which is significant: see
[Types](Types.md#boolean-names). It may then end in `!`, which marks a
declaration that [shadows](Components.md#shadowing) a name in scope, and
is not part of the name it declares: `x!` declares `x`, and `ready?!`
declares `ready?`. A few identifiers ending in `!`, such as `s!` and `m!`,
are Lean tokens, and so cannot be [declared](Components.md#shadowing).
`_` alone is an identifier, the wildcard of a
[pattern](Patterns.md).

As in Lean, `a.b` (with no spaces) is a single token, an identifier with
the components `a` and `b`, as is `a.b.c`. Where `a` is an instance, it
refers to the instance's variable `b` (see
[Instances](Instances.md#instance-variables)). Otherwise `a` is a value, a
variable or a [constant](Items.md#constants), and `a.b` reads its field
`b` (see [Records](Expressions.md#records)) or applies the
[method](Expressions.md#methods) `b` to it. It is never a path. A `!`
ends an identifier, and so does a `?` that no `!` follows, so neither is
followed by `.`. An identifier is a keyword if it is a [reserved
word](#keywords).

`lang::identifier` states which lexemes are identifiers. Lean's
identifiers are a superset of Fren's: they may have `?` and `!` anywhere
after the first character, letters other than ASCII, such as `α`, and
quotes, as in `«a b»`. So that a spec reads alike in both front ends, each
reports what Lean reads as one identifier but Fren does not: the Lean
front end checks each identifier of an item, `use`, claim or check against
this rule (but not of `impl` or `interp`, whose bodies are Lean), and the `fren`
command reads identifiers by Lean's rule too, and reports any that Fren's
would read differently, such as `a?b`, `xα`, or `y!!`. Both read `a!=b`
as `a!` then `=`, so write spaces around `!=` after an identifier.

Some identifiers that end in `!` are Lean tokens, such as `s!` and `m!`,
which Lean reads in preference to an identifier. Where Fren's syntax
expects an identifier, the Lean front end reads these tokens as
identifiers, so both front ends report a declaration of one (see
[Shadowing](Components.md#shadowing)), and the use of an unknown name in
`s!=1`. One case differs, where Lean's parser reports the lexeme before
the Lean front end sees it: a `«` that is never closed is a syntax error
in Lean, while the `fren` command reports that the lexeme is not an
identifier.

The tokens read as identifiers are those that importing `Fren` brings in.
A Lean file that also imports a library adding its own such token, such as
Mathlib's `ring!`, cannot declare that name with `!`: Lean's parser reports
an error there, while the `fren` command, which knows only Fren's imports,
accepts the declaration.

```fren
pub mod lang

pub comp identifier {
    in lexeme: String
    pub det out accepted?

    req rule: accepted? iff lexeme.matches?(r"[A-Za-z_][A-Za-z0-9_']*([.][A-Za-z_][A-Za-z0-9_']*)*[?]?[!]?")

    expect primed: when lexeme = "x'", accepted?
    expect components: when lexeme = "w.x.y?", accepted?
    expect wildcard: when lexeme = "_", accepted?
    expect capitals: when lexeme = "Heat" or lexeme = "x.Y", accepted?
    expect question_last: when lexeme = "a?b" or lexeme = "a?.b", not accepted?
    expect bang: when lexeme = "x!" or lexeme = "ready?!", accepted?
    expect bang_last: when lexeme = "a!?" or lexeme = "a!b" or lexeme = "a!!", not accepted?
    expect letter_first: when lexeme.matches?(r"[0-9'.?!].*"), not accepted?
    expect no_trailing_dot: when lexeme.ends_with?("."), not accepted?
}
```

`lang::identifier_shape` states the shape of an identifier without a
pattern: no component is empty, it starts with neither a digit nor `'`,
`.`, `?` or `!`, it does not end with `.`, a `!` comes only last, once,
and a `?` only last, once, or just before that `!`. `identifier` refines
it. That no component is empty is the emptiness of an intersection of
two regular languages, in the decidable core, but cvc5 does not decide it
within any time limit tried (see [Decidability](Decidability.md#in-practice)), so the
refinement is checked by testing:

```fren
pub comp identifier_shape {
    in lexeme: String
    pub out accepted?

    req no_empty_component: when lexeme.contains?(".."), not accepted?
    req letter_first: when lexeme.matches?(r"[0-9'.?!].*"), not accepted?
    req no_trailing_dot: when lexeme.ends_with?("."), not accepted?
    req question_last: when lexeme.contains?("?") and not (lexeme.ends_with?("?") or lexeme.ends_with?("?!")),
        not accepted?
    req one_question: when lexeme.contains?("??"), not accepted?
    req bang_last: when lexeme.contains?("!") and not lexeme.ends_with?("!"), not accepted?
    req one_bang: when lexeme.contains?("!!"), not accepted?

    expect first_characters: when lexeme in {"1", "1x", "'x", ".x", "?", "?x", "!", "!x"}, not accepted?
}

set_option fren.evidence "tested" in
refine identifier_has_shape: identifier refines identifier_shape
```

Identifiers follow the rule of *maximal munch*: an identifier is the
longest prefix of the remaining input that is one. A `.` continues it
only before a letter or `_`, so `w.x` is one identifier, while in
`f(x).y` the `.` follows `)` and reads the field `y` (see
[Records](Expressions.md#records)). Only a `!` continues an identifier
after its `?`, and nothing after its `!`. `lang::identifier_end` states
where an identifier ends, from the input that remains after it:

```fren
pub comp identifier_end {
    in lexeme: String
    in remaining: String     -- the input after the lexeme
    pub det out ends?

    req maximal_munch: ends? iff (lexeme.ends_with?("!")
        or (lexeme.ends_with?("?") and not remaining.starts_with?("!"))
        or not (remaining.matches?(r"[A-Za-z0-9_'?!].*") or remaining.matches?(r"[.][A-Za-z_].*")))

    expect space_ends: when remaining.starts_with?(" "), ends?
    expect component: when lexeme = "w" and remaining = ".x", not ends?
    expect field_of_call: when lexeme = "w" and remaining = ".(", ends?
    expect after_question: when lexeme = "a?" and remaining = "b", ends?
    expect bang_after_question: when lexeme = "a?" and remaining = "!", not ends?
    expect after_bang: when lexeme = "a!" and remaining = "=b", ends?
}
```

What maximal munch means is that no prefix `p` of `remaining` continues
the identifier: `(lexeme ++ p)` is not one. That quantifies over prefixes,
but the one or two characters after the identifier decide it, since a
`.` continues it only before a letter or `_`. `lang::longest_identifier`
states it so, against `identifier` itself, and `identifier_end` refines
it. Its instances' bindings concatenate, which is outside the [decidable
core](Decidability.md#strings) for a binding, and cvc5 does not decide
them in practice, so the refinement, and `longest_identifier`'s own
checks, are tested:

```fren
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub comp longest_identifier {
    in lexeme: String
    in remaining: String     -- the input after the lexeme
    pub out ends?

    inst w: identifier { lexeme }
    inst one: identifier { lexeme := lexeme ++ remaining.at(0) }
    inst two: identifier { lexeme := lexeme ++ remaining.slice(0, 2) }

    req longest: when w.accepted? and remaining != "", ends? iff not (one.accepted? or two.accepted?)
    req at_end: when remaining = "", ends?

    expect dotted: when lexeme = "w" and remaining = ".x", not ends?
    -- `w.x` is an identifier, so `w` does not end before the `.`; the space
    -- ends `w.x`, not `w`.
    expect dotted_then_space: when lexeme = "w" and remaining = ".x y", not ends?
}

set_option fren.evidence "tested" in
refine identifier_end_is_longest: identifier_end refines longest_identifier
```

## Paths

A path is a sequence of identifiers separated by `::`, such as
`climate::Mode::Heat`. A path may start with `self`, which stands for the
current module (see [Modules and visibility](Modules.md)). `::*` and `::{`
are single tokens and must be written without spaces. `lang::path_shape`
states where `self` may be, over a path's segments: every segment but the
first is in `segs.slice(1, segs.len)`, since `slice` stops at the end.
That is how a rule about every element is said without a quantifier, but
`in` on a sequence that is not a literal is outside the [decidable
core](Decidability.md#sequences), so the rule opts out:

```fren
pub mod lang

set_option fren.lint.undecidable "allow" in
pub comp path_shape {
    in segs: Seq(String)         -- a path's segments
    pub det out accepted?

    assume nonempty: segs != []
    assume identifiers: not "" in segs

    req rule: accepted? iff not "self" in segs.slice(1, segs.len)

    expect self_first: when segs = ["self", "Mode"], accepted?
    expect self_later: when segs.len >= 2 and segs[1] = "self", not accepted?
}
```

## Keywords

Where `Fren.Lang` is open, these are reserved words: Fren's own keywords,
and the keywords of Lean that Fren uses. `lang::reserved_word` states
which:

```fren
pub const RESERVED: Set(String) := {
    "mod", "use", "pub", "ordered", "enum", "struct", "type", "fn", "const", "comp", "expect", "impl",
    "interp", "tested", "trusted", "iff", "and", "or", "union", "inter", "minus", "subset", "join",
    "div", "is", "in", "if", "then", "else", "match", "forall", "refine", "with", "let", "where",
}

pub comp reserved_word {
    in lexeme: String        -- an identifier
    pub det out reserved?

    req rule: reserved? iff lexeme in RESERVED

    expect contextual: when lexeme = "when" or lexeme = "req" or lexeme = "cover" or lexeme = "out", not reserved?
    expect membership: when lexeme = "in", reserved?
    expect pattern_test: when lexeme = "is", reserved?
    expect record_update: when lexeme = "with", reserved?
    expect modifier: when lexeme = "ordered", reserved?
    expect local_definitions: when lexeme = "let" or lexeme = "where", reserved?
}
```

`ordered`, the modifier of an [ordered
enumeration](Items.md#enumerations), is reserved, as `pub` and `enum`
are, since an item can start with it.

Lean reserves its other keywords too, such as `for`, `by` and `fun`, so a
spec read by Lean cannot use them as names. These *contextual keywords*
have special meaning at the start of a construct, and are otherwise
ordinary identifiers:

```
when  unless  not  true  false  det  out  assume  req  cover  inst
```

`true` and `false` are the exception: they are the literals of type
`Bool` wherever an expression is expected, at the start of one or not, so
in `x = true` the `true` is a literal. Nothing could then mention a
declaration named `true` or `false`, so declaring either, as any kind of
name, is an error (`F0220`).

`in` is both the keyword of an input and the [membership
operator](Expressions.md#sets). The `in` of a membership must be on the
same line as the end of its left operand: an `in` at the start of a line
starts an input. It is also the keyword that ends the definitions of a
[`let`](Let.md), so within them, outside brackets, `in` is never a
membership. Likewise, `mod` is both the keyword of a module and the
[remainder](Expressions.md#division-and-remainder) operator, and the `mod`
of a remainder must be on the line where its left operand ends: a `mod` at
the start of a line starts a module, so that a constant's value followed by
`mod m` on the next line is not read as a remainder.

## Literals

Integer literals are Lean's, and unbounded: decimal, such as `0` or
`120`, or hexadecimal, binary or octal after `0x`, `0b` or `0o`, such as
`0x1F`, `0b101` or `0o17`. A `_` may separate digits, as in `1_000`, and
may follow the base, as in `0x_FF`, but a literal ends in a digit. They
have type `Int`. A negative number is written with unary minus, `-1` (see
[Expressions](Expressions.md)). `true` and `false` are the literals of type
`Bool`.

Like an identifier, a number is as long as it can be, as Lean reads an
integer: after a base, it runs over that base's digits and `_`s, and
otherwise over decimal digits and `_`s. So `0b12` is `0b1` then `2`, and
`1_foo` starts with `1_`, which is not an integer literal. Fren has no
scientific literals, so in `1.5` and `1e3` the number is `1`, where Lean
would read on. `lang::integer_literal` states
which lexemes are integer literals. Lean reads `0_1` as a number but
cannot give its value, so it is not one.

As for identifiers, the two front ends report most malformed numbers
differently. Lean's own parser rejects `1_`, `0x` and `0b2` before the
Lean front end sees them, so only `0_1` and its like reach Fren's rule
there, while the `fren` command reports all of them as not integer
literals:

```fren
pub comp integer_literal {
    in lexeme: String
    pub det out accepted?

    req rule: accepted? iff ((lexeme.matches?(r"[0-9]([0-9_]*[0-9])?") and not lexeme.starts_with?("0_"))
        or lexeme.matches?(r"0[xX][0-9a-fA-F_]*[0-9a-fA-F]") or lexeme.matches?(r"0[bB][0-1_]*[0-1]")
        or lexeme.matches?(r"0[oO][0-7_]*[0-7]"))

    expect decimal: when lexeme = "120" or lexeme = "0", accepted?
    expect bases: when lexeme = "0x1F" or lexeme = "0b101" or lexeme = "0o17", accepted?
    expect separated: when lexeme = "1_000" or lexeme = "0x_FF", accepted?
    expect digit_last: when lexeme.ends_with?("_"), not accepted?
    expect base_needs_digits: when lexeme = "0x" or lexeme = "0b", not accepted?
    expect leading_zero_separator: when lexeme = "0_1", not accepted?
}
```

String literals are Lean's, such as `"ab"` or `"a\n"`, and have type
`String`. A literal may use Lean's escape sequences: `\\`, `\"`, `\'`,
`\n`, `\t`, `\r`, `\xHH` and `\uHHHH`. A raw literal, `r"..."` or
`r#"..."#`, has none. A literal may contain only characters up to
`U+2FFFF` (see [Strings](Types.md#strings)), and ends on the line it
starts.

`lang::escape_sequence` states the escape sequences, from the input after
a `\`, and the length of each in the source, the `\` included. Any other
character after a `\` is an error:

```fren
pub comp escape_sequence {
    in remaining: String     -- the input after a `\` in a literal
    pub det out accepted?
    pub det out length: Int

    req rule: accepted? iff remaining.matches?(r#"([nrt\\"']|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}).*"#)
    req single: when accepted? and remaining.matches?(r#"[nrt\\"'].*"#), length = 2
    req byte: when accepted? and remaining.starts_with?("x"), length = 4
    req unicode: when accepted? and remaining.starts_with?("u"), length = 6
    req rejected: when not accepted?, length = 0

    expect no_classes: when remaining.starts_with?("d"), not accepted?
    expect short_hex: when remaining = "x4", not accepted?
    expect accepted_length: when accepted?, length >= 2
}
```

`lang::escape_text` says what the length is: the `\` and exactly the
characters of one escape sequence. `escape_sequence` refines it. Reading
that many characters is a slice of a length that is not a constant,
outside the [decidable core](Decidability.md#strings), so `escape_text`
allows it, and the refinement is checked by testing:

```fren
set_option fren.lint.undecidable "allow" in
pub comp escape_text {
    in remaining: String     -- the input after a `\` in a literal
    pub out accepted?
    pub out length: Int

    req exact: when accepted?, remaining.slice(0, length - 1).matches?(r#"[nrt\\"']|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}"#)
    req rejected: when not accepted?, length = 0
}

set_option fren.evidence "tested" in
refine escape_sequence_is_exact: escape_sequence refines escape_text
```

`lang::escape_start` says which input starts an escape sequence again,
character by character rather than by one pattern for the whole sequence,
so that each statement checks the other: a character that one accepts and
the other does not breaks the refinement. `escape_sequence` refines it,
and the solver decides it:

```fren
pub comp escape_start {
    in remaining: String     -- the input after a `\` in a literal
    pub out accepted?

    req escapes: accepted? iff (remaining.starts_with?("n") or remaining.starts_with?("r")
        or remaining.starts_with?("t") or remaining.starts_with?("\\") or remaining.starts_with?("\"")
        or remaining.starts_with?("'")
        or (remaining.starts_with?("x") and remaining.at(1).matches?(r"[0-9a-fA-F]")
        and remaining.at(2).matches?(r"[0-9a-fA-F]"))
        or (remaining.starts_with?("u") and remaining.at(1).matches?(r"[0-9a-fA-F]")
        and remaining.at(2).matches?(r"[0-9a-fA-F]") and remaining.at(3).matches?(r"[0-9a-fA-F]")
        and remaining.at(4).matches?(r"[0-9a-fA-F]")))
}

refine escape_sequence_starts: escape_sequence refines escape_start
```

## Punctuators

```
::  ::*  ::{  :  :=  ,  (  )  {  }  [  ]  .  ..  ..=  =>  |  =  !=  <  <=  >  >=  +  ++  -  *
```

`..` and `..=` are written only in a [range pattern](Patterns.md#kinds-of-pattern).

`_` is an [identifier](#identifiers). `#fren_check` and `#fren_trace` are
commands, single tokens that start with `#`.

Operators of other languages are errors, with a message that says what to
write instead: `==` (write `=`), `&&` (write `and`), `||` (write `or`), `!`
(write `not`; a `!` directly after an identifier is part of it) and,
outside a [`match` arm](Expressions.md#matches), `=>`
(write `when a, b`) and `|` (write `or`), and `/` and `%` (write `div`
and `mod`, which [divide by a constant](Expressions.md#division-and-remainder)). The first
three are lexed as punctuators, so that the message names them as Lean's
does.

`<-` is a punctuator too, since it is a Lean token, and Fren is lexed as
Lean is: `x <- 1` is `x`, `<-` and `1`, not `x < -1`. Fren has no operator
`<-`, so it is an error (F0121), with the fix `< -`. It is the only Lean
token made of Fren punctuators that could otherwise be read as Fren: the
others, such as `->`, `<->`, `|>`, `<|`, `>>`, `..` and `.(`, would be
punctuators that never follow one another in an expression, so they are
errors either way.

Punctuators follow maximal munch too, so `::*` is one punctuator and not
`::` followed by `*`. A punctuator that extends a shorter one does so one
character at a time, through punctuators (`:`, `::`, `::*`), so one
character of lookahead decides whether a punctuator ends. Two punctuators
extend none: `!=` and `&&` start with `!` and `&`, which are not
punctuators.
`lang::punctuator_end` states this. The lexer asks only where a
punctuator that it has read ends, never where some other text would, so
the rule assumes that `lexeme` is a punctuator:

```fren
-- Longest first, as the lexer tries them.
pub const PUNCTUATORS: Set(String) := {
    "::*", "::{", "..=", "::", "..", "==", "=>", "&&", "||", "|", "!=", "<=", "<-", ">=", ":=", "{", "}",
    "(", ")", "[", "]", ",", ":", ".", "*", "=", "<", ">", "++", "+", "-",
}

pub comp punctuator {
    in lexeme: String
    pub det out accepted?

    req rule: accepted? iff lexeme in PUNCTUATORS

    -- The punctuators listed above, the three of other languages, and
    -- Lean's `<-`.
    expect listed: accepted? iff lexeme in {
        "::", "::*", "::{", ":", ":=", ",", "(", ")", "{", "}", "[", "]", ".", "..", "..=", "=>", "|",
        "=", "!=", "<", "<=", ">", ">=", "+", "++", "-", "*", "==", "&&", "||", "<-",
    }
}

pub comp punctuator_end {
    in lexeme: String
    in remaining: String     -- the input after the lexeme
    pub det out ends?

    assume a_punctuator: lexeme in PUNCTUATORS

    out longer: String := lexeme ++ remaining.at(0)
    inst one: punctuator { lexeme := longer }
    req maximal_munch: ends? iff (remaining = "" or not one.accepted?)

    expect path_glob: when lexeme = "::" and remaining.starts_with?("*"), not ends?
    expect no_triple: when lexeme.len = 3, ends?
    expect lean_arrow: when lexeme = "<" and remaining.starts_with?("-"), not ends?
}
```

That one character decides is a property of `PUNCTUATORS`, which
`lang::longest_punctuator` states: a punctuator ends exactly when neither
one nor two more characters make a longer one. `punctuator_end` refines
it, so no punctuator that extends another is reached only through a
string that is not one. Both rules are about extending a punctuator, and
say nothing of `!=` and `&&`, which extend none.
The instances' bindings concatenate, outside the core for a binding, so
the refinement is tested:

```fren
set_option fren.lint.undecidable "allow" in
set_option fren.evidence "tested" in
pub comp longest_punctuator {
    in lexeme: String
    in remaining: String     -- the input after the lexeme
    pub out ends?

    assume a_punctuator: lexeme in PUNCTUATORS

    inst one: punctuator { lexeme := lexeme ++ remaining.at(0) }
    inst two: punctuator { lexeme := lexeme ++ remaining.slice(0, 2) }

    req longest: when remaining != "", ends? iff not (one.accepted? or two.accepted?)
    req at_end: when remaining = "", ends?
}

set_option fren.evidence "tested" in
refine punctuator_end_is_longest: punctuator_end refines longest_punctuator
```

## Tokens apart

Identifiers, reserved words, punctuators and literals are told apart
without depending on which rule is tried first. Two kinds overlap with
identifiers in shape, and each overlap is settled: a reserved word has the
shape of an identifier, which is why it must be reserved, and reserving it
settles which it is; and the literals `true` and `false` are
[contextual keywords](#keywords), not reserved, so that, as for the
other contextual keywords, the context settles whether one is a literal
or an identifier. A punctuator is
neither an identifier nor a reserved word; the second follows from the
first and `reserved_are_identifiers`, and is stated for the reader. Any
other literal starts with a digit or a double quote, or, for a raw string,
with `r` and then a double quote or `#`, which no identifier or punctuator
starts with, so its first two characters tell it apart:

```fren
expect reserved_are_identifiers: forall (r: reserved_word) (i: identifier),
    when r.lexeme = i.lexeme and r.reserved?, i.accepted?

expect punctuators_not_identifiers: forall (p: punctuator) (i: identifier),
    when p.lexeme = i.lexeme and p.accepted?, not i.accepted?

expect punctuators_not_reserved: forall (p: punctuator) (r: reserved_word),
    when p.lexeme = r.lexeme and p.accepted?, not r.reserved?
```
