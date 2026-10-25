# Literals

## Invisible characters

`invisible_characters` fires on a string literal that contains a
zero-width or invisible character: U+200B (zero width space), U+00AD (soft
hyphen) or U+2060 (word joiner). It also fires on a string literal or a
comment that contains a bidirectional control, U+202A to U+202E or U+2066
to U+2069, or U+FEFF (zero width no-break space). An invisible character
makes two literals that look the same differ. A bidirectional control can
make text display in an order other than the one it is read in, so that
what a reader sees is not what it means, as in the "trojan source"
attacks.

It is reported once for each literal or comment, at it, and the message
names the characters. In a literal, the fix writes each as an escape, such
as `\u200B` (see [Literals](../../Lang/Lexical.md#literals)), which keeps the
value and lets a deliberate use stay; a raw literal, which has no escapes,
becomes an ordinary one, with `\\` and `\"` for its `\` and `"`. In a
comment, the fix removes them, which changes no meaning.
`lint::invisible_character` states which characters it reports, by code
point:

```fren
pub mod lint

pub comp invisible_character {
    in code: Nat         -- the character's code point
    in comment?          -- it is in a comment, rather than a string literal
    pub det out fires?

    -- U+202A to U+202E, U+2066 to U+2069 and U+FEFF anywhere; U+00AD,
    -- U+200B and U+2060 in a literal.
    ensure rule: fires? iff (8234 <= code <= 8238 or 8294 <= code <= 8297
        or code = 65279 or (not comment? and code in {173, 8203, 8288}))

    expect controls_in_comments: when code = 8238, fires?
    expect ascii_never: when code < 128, not fires?
}
```

The level that applies to it is the one in effect at the item that the
literal or comment is in. A comment between two items is in the one
before it, and a comment before the first item is in the first, but for
a `set_option`, which leaves its comments to the item after it, so that
the level it sets applies to them.

## Tests of literals

`const_is_empty` fires on a test of a literal whose value is fixed by the
literal, which is probably not the literal meant. It has no fix, and its
message says what the test always is. It fires on:

- a comparison of the `len` of a string or sequence literal with an integer
  literal, such as `"ab".len = 0` or `[1, 2].len > 0`, with the literal on
  either side;
- a comparison of the `card` of a set or relation literal that
  [`card_zero`](../Style.md#empty-collections) fires on, a test of whether it
  is empty, such as `{a}.card = 0`;
- `e = E` or `e != E`, where `E` is `""`, `[]` or `{}`, and `e` a string,
  sequence, set or relation literal that is not empty, such as `"ab" = ""`,
  on either side.

A string literal has as many characters as its value, and a sequence
literal as many elements as it is written with, so the length is fixed. A
set literal's elements may be equal, so `{a, b}.card` is `1` or `2`, but it
is `0` exactly when the literal is `{}`, so only whether it is empty is
fixed. Where `const_is_empty` fires on a length, [`length_zero` and
`card_zero`](../Style.md#empty-collections) do not, since writing `"ab" = ""`
would keep the mistake, and neither does
[`absurd_extreme_comparisons`](Comparisons.md), since the message already
says what the comparison always is: `"ab".len < 0` gets only
`const_is_empty`. Where `const_is_empty` does not fire,
`absurd_extreme_comparisons` still does, as on `{a}.card >= 0`, which is
not a test of whether the set is empty. `"" = ""` is left to [`eq_op`](Expressions.md#operands-written-the-same),
and `[].len` and `{}.card` are errors, since `[]` and `{}` have no type
there. `lint::const_is_empty` states when it fires on a length, and what
the comparison always is, and `lint::const_empty_equation` the same for an
equation with an empty literal:

```fren
pub comp const_is_empty {
    in op: Comparison
    in bound: Int        -- the integer literal compared with
    in left?             -- the length is the left operand, rather than the right
    in set?              -- the literal is a set's or relation's
    in n: Nat            -- its characters, or the elements it is written with
    pub det out fires?
    pub det out value?   -- what the comparison always is, where it fires

    inst p: length_zero { op, bound, left? }

    ensure rule: fires? iff (not set? or p.fires?)
    ensure value: value? iff (if set? then (p.empty? iff n = 0)
        else compares?(op, if left? then n else bound, if left? then bound else n))
}

pub comp const_empty_equation {
    in equal?            -- the operator is `=`, rather than `!=`
    in n: Nat            -- the characters or elements of the literal that is not `E`
    pub det out fires?
    pub det out value?

    ensure rule: fires? iff n > 0
    ensure value: value? iff (equal? iff n = 0)
}
```

The value is exact: where the lint fires, the comparison has it for every
length that the literal can have, its number of characters or elements, or
for a set, any `card` from `1` to that number if it is not empty:

```fren
comp const_is_empty_exact {
    in op: Comparison
    in bound: Int
    in left?
    in set?
    in n: Nat
    in length: Int       -- the literal's `len` or `card`

    assume lengths: (if set? then (if n = 0 then length = 0 else 1 <= length <= n)
        else length = n)

    inst p: const_is_empty { op, bound, left?, set?, n }

    expect exact: when p.fires?,
        compares?(op, if left? then length else bound, if left? then bound else length) iff p.value?
}
```

## Ranges of characters

`almost_complete_range` fires on a range in a class of a
[pattern](../../Lang/Expressions.md#patterns) that is one character short of a
whole alphabet, and is fixable: `a-y` and `b-z`, `A-Y` and `B-Z`, and `0-8`.
A range is from its first character to its last, both included, so `[a-y]`
leaves out `z`, which is probably a mistake. The fix is the whole range,
`a-z`, `A-Z` or `0-9`, and the message is reported once for the literal,
whose fix completes each such range in it, writing the literal as
[`manual_pattern_char_comparison`](../Style.md#classes-of-characters)'s fix
does. Only the literal changes, so the fix keeps the guards.

`1-9` is not one of them: it is often meant, as in `[1-9][0-9]*`, a number
without a leading zero. `0-8` has no such use, since `0-7` is the octal
digits. `lint::almost_complete_range` states this, from the code points of
the characters before and after `-`, as [`lang::char_range`](../../Lang/Expressions.md#patterns)
does: `a` is 97, `A` is 65 and `0` is 48:

```fren
pub comp almost_complete_range {
    in low: Int          -- the code point of the character before `-`
    in high: Int         -- of the character after it
    pub det out fires?
    pub det out whole_low: Int   -- the range of the fix, from this code point
    pub det out whole_high: Int  -- to this one

    ensure rule: fires? iff ((low in {97, 98, 65, 66} and high = low + 24) or (low = 48 and high = 56))
    ensure fix_low: whole_low = (if fires? and low in {98, 66} then low - 1 else low)
    ensure fix_high: whole_high = (if fires? and high in {121, 89, 56} then high + 1 else high)

    expect not_digits: when low = 49 and high = 57, not fires?
    expect whole: when fires?, whole_high - whole_low = 25 or (whole_low = 48 and whole_high = 57)
}
```

## Dots in patterns

`literal_dot_in_pattern` fires on a `.` in a
[pattern](../../Lang/Expressions.md#patterns) between two letters or digits,
as in `r"v1.2"` or `r".*file.txt"`, and is fixable. A `.` matches any one
character, so `r"v1.2"` matches `"v1x2"` too, but between two letters or
digits it is probably meant as a dot. The `.` must be neither escaped nor
in a class, where it is a dot already, and so must the letters or digits:
in `r"[0-9]{3}.[0-9]{4}"`, the `.` is between a `}` and a `[`, and in
`r"\..x"`, after an escape, so neither fires. A `.` followed by a letter
or digit is not followed by a quantifier, as the `.` of `.*` is. The fix
writes each such `.` as `[.]`, and the message is reported once for the
literal, whose fix writes the literal as
[`manual_pattern_char_comparison`](../Style.md#classes-of-characters)'s fix
does. It writes `[.]` rather than `\.`, since `\.` is not an
[escape](../../Lang/Lexical.md#literals) in a string literal that is
not raw. Fren's own patterns write a dot as `[.]` or `\.`. The fix changes
what the pattern matches, to what it probably meant, and only the literal
changes, so it keeps the guards. `lint::literal_dot_in_pattern` states
when it fires:

```fren
pub comp literal_dot_in_pattern {
    in before?           -- a letter or digit, neither escaped nor in a class, is directly before the `.`
    in after?            -- one is directly after it
    pub det out fires?

    ensure rule: fires? iff (before? and after?)
}
```

`lint::literal_dot_fixed` and `lint::literal_dot_value` check, with a
[refinement](../../Lang/Refinement.md) each way, that the fix of `r"v1.2"`
matches exactly the string `"v1.2"`, and `lint::literal_dot_written` that
the pattern as written matches `"v1x2"` too:

```fren
set_option fren.lint.literal_dot_in_pattern "allow" in
pub comp literal_dot_written {
    in s: String
    pub det out v? := s.matches?(r"v1.2")

    expect any_character: when s = "v1x2", v?
}

pub comp literal_dot_fixed {
    in s: String
    pub det out v? := s.matches?(r"v1[.]2")
}

pub comp literal_dot_value {
    in s: String
    pub det out v? := s = "v1.2"
}

refine literal_dot_sound: literal_dot_value refines literal_dot_fixed
refine literal_dot_complete: literal_dot_fixed refines literal_dot_value
```
