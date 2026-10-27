# Source text

These lints of the `pedantic` group look at how a spec is written: the
code points of its string literals, and the commas of its lists. Both are
`allow` by default.

## Unicode normalization

`unicode_not_nfc` fires on a string literal, raw ones too, whose value is
not in Unicode Normalization Form C (NFC), as Unicode Standard Annex #15
defines it. One text can be written with different code points: `é` is
the one code point U+00E9, or `e` and then U+0301, a combining acute
accent. The two are *canonically equivalent*, and look the same, but
strings compare by code point, so `"e\u0301" = "\u00e9"` is
`false`. NFC writes each text in one way, with its characters composed
where Unicode composes them, and text is usually in NFC, as most
keyboards write it. A string not in NFC is never equal to one in NFC, so
a literal that is not may never equal the input it is meant for. It is
`pedantic`, as Clippy's lint of the same name is. The message names the
code points that differ, since they look the same, and those that NFC
writes for them.

The lint looks at the literal's value, so `"\u0065́"`, whose escape
sequence `\u0065` is `e`, is reported too. NFC is computed exactly, from
the tables of one version of Unicode, 15.0: a string is decomposed
canonically, its combining marks are put in their canonical order, and it
is composed canonically, with the algorithms of the annex. A literal with
a code point that Unicode 15.0 does not assign is not looked at, since a
later version may give that code point a combining class or a
decomposition, and so a different NFC: the lint never reports a literal
that is in NFC under a later version.

[`non_ascii_literal`](../Restriction.md), of the `restriction` group, also
fires on each literal that this lint reports, since a literal not in NFC
has a character beyond ASCII: it asks for the character as an escape
sequence wherever one is written, for a project that rules them out, and
this lint for the literal in NFC.

It has no fix, since writing the literal in NFC changes what it means:
its value becomes another string, canonically equivalent to the one
before, which is what the literal shows, but not what it is. `fren fix`
keeps what the spec means (see [Fixing lints](../../Lint.md#fixing-lints)),
so it leaves the literal as it is, and the message suggests the literal
in NFC instead, for the writer to decide. The suggestion keeps the
literal's delimiters: `"`, or `r"` or `r#"` and the `"` or `"#` after it.
It is made only for a literal without an escape sequence, a raw one or
one without a `\`, whose value is its text between the delimiters, so
that NFC of the value is NFC of the text. For a literal with an escape
sequence, the message says to write it so that its value is in NFC:
which characters to write as escape sequences is the writer's choice.
NFC never writes a `"`, a `\` or a `#`, so the suggestion never ends the
literal early. `lint::unicode_not_nfc` states when it fires, and when it
suggests a literal:

```fren
pub mod lint

set_option fren.evidence "enumerated" in
pub proc unicode_not_nfc(
    nfc?,                -- the literal's value is in NFC
    assigned?,           -- Unicode 15.0 assigns each of its code points
    escapes?,            -- it is not raw, and has an escape sequence
): (
    det fires?,
    det suggested?,         -- the message suggests the literal in NFC
) {
    ensure rule: fires? iff (assigned? and not nfc?)
    ensure suggestion: suggested? iff (fires? and not escapes?)

    expect unknown: when not assigned?, not fires?
}
```

NFC cannot be stated in Fren without the tables of Unicode, so the
[refinements](../../Lang/Refinement.md) below check the suggestion for one
literal, `"café"`, whose last two code points are `e` and U+0301,
against an abstraction of NFC. The input `s` is in NFC, so it has no `e`
followed by U+0301, and its decomposition, as far as `é` goes, is `s` with
each `é` written as `e` and U+0301. The literal as written is compared
with the decomposition, and the literal suggested with `s` itself, and the
solver checks that the two agree: the literals are canonically
equivalent. `nfc_written` also expects what the message says, that the
literal never equals `s`. `contains?` and `replace_all` of a string that
is not a constant are outside the [decidable
core](../../Lang/Decidability.md#strings), so both opt out:

```fren
set_option fren.lint.unicode_not_nfc "allow" in
set_option fren.lint.undecidable "allow" in
pub proc nfc_written(s: String): (det cafe?) {
    assume composed: not s.contains?("e\u0301")
    out cafe? := s.replace_all("\u00e9", "e\u0301") = "café"

    expect never_equal: s != "café"
}

set_option fren.lint.unicode_not_nfc "allow" in
set_option fren.lint.undecidable "allow" in
pub proc nfc_fixed(s: String): (det cafe?) {
    assume composed: not s.contains?("e\u0301")
    out cafe? := s = "café"
}

refine nfc_sound: nfc_fixed refines nfc_written
refine nfc_complete: nfc_written refines nfc_fixed
```

## Trailing commas

`unnecessary_trailing_comma` fires on a comma after the last element of a
list, where no line ends between the comma and the `}`, `]` or `)` that
closes the list, as in `{a, b,}`, `[a, b, ]` or `p(a, b,)`. A trailing
comma is for a list whose closing token starts a line, as [`fren fmt`](../../Fmt.md#trailing-commas)
writes it, so that an element is added by adding a line; on the line of
its closing token, it adds nothing. It is `pedantic`, as Clippy's lint of the
same name is. A line comment after the comma ends its line, as in `[a, b,
-- c` with the `]` on the next line, which is left as it is.

The lists that may end with a comma are those in braces, the elements of
a set literal, the bindings of a refinement, the variants
of an enumeration, the fields of a record, of a record literal or of a
record update, the arms of a `match` and the paths of a `use ...::{}`,
those in brackets, the elements of a sequence literal, and three in
parentheses: the parameters and the results of a procedure and the
arguments of a call. Any other list in parentheses, such as the arguments
of an application or the parameters of a function, may not end with a
comma, which is an error (`F0104`), and the files of a `tested` claim have
no closing token. So a comma followed by a `}`, `]` or `)` is a trailing
comma, and both front ends find it from the
tokens: the binary from the tokens of the item, and Lean from those of the
command.

The fix removes the comma. It changes no expression, so it keeps what the
spec means and every guard. It leaves the space before the `}` or `]` as
it is, which `fren fix --fmt` then formats. `fren fmt` removes the same
commas from a list in braces, which is not vertical where the `}` follows
the comma on its line. It leaves the commas of a sequence literal as they
are, but never adds one there. `lint::unnecessary_trailing_comma` states
when it fires, and [`fmt::trailing_comma_lint`](../../Fmt.md#trailing-commas)
that `fren fmt` removes what it reports in braces:

```fren
set_option fren.evidence "enumerated" in
pub proc unnecessary_trailing_comma(
    line_break?,         -- a line ends between the trailing comma and the `}` or `]`
): (det fires?) {
    ensure rule: fires? iff not line_break?
}
```

The refinements below check the fix of a sequence literal: a procedure as
written, one as fixed, and a refinement each way. `fren fmt` would remove
the comma of a list in braces, so only the sequence keeps it here:

```fren
set_option fren.lint.unnecessary_trailing_comma "allow" in
pub proc trailing_comma_written(x: Int): (det q: Seq<Int>) {
    out q := [x, 1,]
}

pub proc trailing_comma_fixed(x: Int): (det q: Seq<Int>) {
    out q := [x, 1]
}

refine trailing_comma_sound: trailing_comma_fixed refines trailing_comma_written
refine trailing_comma_complete: trailing_comma_written refines trailing_comma_fixed
```
