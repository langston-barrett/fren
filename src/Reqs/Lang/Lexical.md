# Lexical structure

Fren is lexed as Lean is, so that a spec can be part of a Lean file.

## Comments

`--` starts a comment that runs to the end of the line. `/-` and `-/`
delimit a block comment, and block comments nest.

## Identifiers

Identifiers are ASCII: a letter or `_`, then letters, digits, `_` and
`'`. An identifier may end in `?`, which is significant: see
[Types](Types.md#boolean-names). `_` alone is an identifier, the wildcard
of a [`match` arm](Expressions.md#matches).

As in Lean, `a.b` (with no spaces) is a single token, an identifier with
the components `a` and `b`, as is `a.b.c`. It refers to the variable `b`
of the instance `a` (see [Instances](Instances.md#instance-variables)),
the field `b` of the record `a` (see [Records](Expressions.md#records)), or
the [method](Expressions.md#methods) `b` applied to `a`, which may be a
variable or a [constant](Items.md#constants). It is never a path. A `?`
ends an identifier, so it is never followed by `.`. An identifier is a
keyword if it is a [reserved word](#keywords).

`lang::identifier` states which lexemes are identifiers. Lean's
identifiers are a superset of Fren's: they may have `?` and `!` anywhere
after the first character, letters other than ASCII, such as `α`, and
quotes, as in `«a b»`. So that a spec reads alike in both front ends, each
reports what Lean reads as one identifier but Fren does not: the Lean
front end checks each identifier against this rule, and the `fren`
command reports a lexeme that Lean's rule would read further than Fren's,
such as `a?b`, or `y!` in `y!=1`. Write spaces around `!=` after an
identifier.

```fren
pub mod lang

pub comp identifier {
    in lexeme: String
    pub det out accepted?

    req rule: accepted? iff lexeme.matches?(r"[A-Za-z_][A-Za-z0-9_']*([.][A-Za-z_][A-Za-z0-9_']*)*[?]?")

    expect primed: when lexeme = "x'", accepted?
    expect components: when lexeme = "w.x.y?", accepted?
    expect wildcard: when lexeme = "_", accepted?
    expect question_last: when lexeme = "a?b" or lexeme = "a?.b", not accepted?
    expect letter_first: when lexeme.matches?(r"[0-9'.?].*"), not accepted?
    expect no_trailing_dot: when lexeme.ends_with?("."), not accepted?
    -- Stronger: no component is empty anywhere, `when
    -- lexeme.contains?(".."), not accepted?`. That is the emptiness of an
    -- intersection of two regular languages, in the decidable core, but cvc5
    -- times out on it.
}
```

Identifiers follow the rule of *maximal munch*: an identifier is the
longest prefix of the remaining input that is one. A `.` continues it
only before a letter or `_`, so `w.x` is one identifier, while in
`f(x).y` the `.` follows `)` and reads the field `y` (see
[Records](Expressions.md#records)). Nothing continues an identifier after
its `?`. `lang::identifier_end` states where an identifier ends, from the
input that remains after it:

```fren
pub comp identifier_end {
    in lexeme: String
    in remaining: String     -- the input after the lexeme
    pub det out ends?

    req maximal_munch: ends? iff (lexeme.ends_with?("?")
        or not (remaining.matches?(r"[A-Za-z0-9_'?].*") or remaining.matches?(r"[.][A-Za-z_].*")))

    expect space_ends: when remaining.starts_with?(" "), ends?
    expect component: when lexeme = "w" and remaining = ".x", not ends?
    expect field_of_call: when lexeme = "w" and remaining = ".(", ends?
    expect after_question: when lexeme = "a?" and remaining = "b", ends?
    -- Stronger, and what maximal munch means: no prefix `p` of `remaining`
    -- continues the identifier, `not (lexeme ++ p).matches?(...)` for every
    -- `p`. That quantifies over prefixes, so instead these would check the
    -- one or two characters that decide it, against `identifier`:
    --
    --     out longer: String := lexeme ++ remaining.slice(0, 1)
    --     inst w: identifier { lexeme }
    --     inst one: identifier { lexeme := longer }
    --     expect longest: when w.accepted? and ends? and remaining != "",
    --         not one.accepted?
    --
    -- with the same for two characters, and the converse, that an
    -- identifier that does not end is continued by one or two. Each is a
    -- regular constraint with straight-line `++`, inside the decidable
    -- core. cvc5 decides `longest` for the `fren` command in under a second,
    -- but times out on it through the Lean front end, and on the others
    -- through both.
}
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
    "mod", "use", "pub", "enum", "struct", "type", "fn", "const", "comp", "expect", "impl", "interp",
    "tested", "trusted", "iff", "and", "or", "union", "inter", "minus", "subset", "join",
    "in", "if", "then", "else", "match", "forall",
}

pub comp reserved_word {
    in lexeme: String        -- an identifier
    pub det out reserved?

    req rule: reserved? iff lexeme in RESERVED

    expect contextual: when lexeme = "when" or lexeme = "req" or lexeme = "out", not reserved?
    expect membership: when lexeme = "in", reserved?
}
```

Lean reserves its other keywords too, such as `for`, `by` and `fun`, so a
spec read by Lean cannot use them as names. These *contextual keywords*
have special meaning at the start of a construct, and are otherwise
ordinary identifiers:

```
when  unless  not  true  false  det  out  assume  req  inst
```

`in` is both the keyword of an input and the [membership
operator](Expressions.md#sets). The `in` of a membership must be on the
same line as the end of its left operand: an `in` at the start of a line
starts an input.

## Literals

Integer literals are decimal and unbounded, such as `0` or `120`. They have
type `Int`. A negative number is written with unary minus, `-1` (see
[Expressions](Expressions.md)). `true` and `false` are the literals of type
`Bool`.

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

## Punctuators

```
::  ::*  ::{  :  :=  ,  (  )  {  }  [  ]  .  =>  |  =  !=  <  <=  >  >=  +  ++  -  *
```

`_` is an [identifier](#identifiers). `#fren_check` and `#fren_trace` are
commands, single tokens that start with `#`.

Operators of other languages are errors, with a message that says what to
write instead: `==` (write `=`), `&&` (write `and`), `||` (write `or`), `!`
(write `not`) and, outside a [`match` arm](Expressions.md#matches), `=>`
(write `when a, b`) and `|` (write `or`). There is no division. The first
three are lexed as punctuators, so that the message names them as Lean's
does.

Punctuators follow maximal munch too, so `::*` is one punctuator and not
`::` followed by `*`. A punctuator that extends a shorter one does so one
character at a time, through punctuators (`:`, `::`, `::*`), so one
character of lookahead decides whether a punctuator ends. `lang::punctuator_end` states
this, for a `lexeme` that is a punctuator:

```fren
-- Longest first, as the lexer tries them.
pub const PUNCTUATORS: Set(String) := {
    "::*", "::{", "::", "==", "=>", "&&", "||", "|", "!=", "<=", ">=", ":=", "{", "}",
    "(", ")", "[", "]", ",", ":", ".", "*", "=", "<", ">", "++", "+", "-",
}

pub comp punctuator {
    in lexeme: String
    pub det out accepted?

    req rule: accepted? iff lexeme in PUNCTUATORS
}

pub comp punctuator_end {
    in lexeme: String
    in remaining: String     -- the input after the lexeme
    pub det out ends?

    out longer: String := lexeme ++ remaining.slice(0, 1)
    inst one: punctuator { lexeme := longer }
    req maximal_munch: ends? iff (remaining = "" or not one.accepted?)

    inst p: punctuator { lexeme }
    expect path_glob: when lexeme = "::" and remaining.starts_with?("*"), not ends?
    expect no_triple: when p.accepted? and lexeme.len = 3, ends?
}
```
