# Formatting

```
fren fmt [--check] [--ignore GLOB]... FILE...
```

`fren fmt` rewrites spec files in Fren's standard layout. With `--check`, it
changes nothing, and instead prints what it would change, as a diff on
standard output. With `--ignore GLOB`, it skips the files that match the
glob, as if they were not given, so that a list of files, such as every
spec in a repository, can leave out some that are deliberately not
formatted. `*` matches within a path segment, and `**` any number of
segments, as for [`fren trace --tests`](Trace.md). A file whose name ends in `.md` is a [Markdown
spec](Markdown.md): its ```` ```fren ```` blocks are read together, as
`fren check` reads them, but each is laid out as if it started a file, and
everything else is kept as it is. Any other file is read as
Fren source.

```fren
pub mod fmt
```

The formatter changes whitespace, the commas at the end of lists (see
[Trailing commas](#trailing-commas)), and the order and grouping of imports
(see [Imports](#imports)). It keeps every comment, and it keeps the line
breaks: it never breaks a long line or joins short ones, except to merge
imports. On each line, it decides the indentation and the spaces between
tokens; across lines, how many blank lines separate them. For example,

```text
use climate::Mode::Heat
pub enum Mode {Heat,Cool}
comp   c{
in t:Int -- the temperature
      pub out mode:Mode
  req r :mode = if t< 18 then Mode::Heat else Mode::Cool


}
```

is formatted as

```text
use climate::Mode::Heat
pub enum Mode { Heat, Cool }
comp c {
    in t: Int  -- the temperature
    pub out mode: Mode
    req r: mode = if t < 18 then Mode::Heat else Mode::Cool
}
```

The layout is chosen so that a change to a spec changes as few lines as
possible: adding a member, an element of a list or an import adds a line,
and changes no other line.

A file that cannot be lexed or parsed is not formatted: its error is
reported as `fren check` reports it, and the file is left as it is. Other
static errors, such as an unknown name, do not stop formatting.

## Safety

Formatting keeps the meaning of a file. `fmt::safe` states this for a file
that parses: apart from the trailing commas of lists and the imports of
each [block](#imports), its tokens are the same after formatting; each
block imports the same paths, as often; its comments are the same, in the
same order; and formatting it again changes nothing.

```fren
pub comp safe {
    in parsed?               -- the file lexes and parses
    pub out same_tokens?     -- the tokens are the same, but for trailing commas and import blocks
    pub out same_imports?    -- each import block imports the same paths, as often
    pub out same_comments?   -- the comments are the same, in the same order
    pub out stable?          -- formatting the result again changes nothing

    req tokens: when parsed?, same_tokens?
    req imports: when parsed?, same_imports?
    req comments: when parsed?, same_comments?
    req idempotent: when parsed?, stable?
}
```

## Spaces

Within a line, two tokens are separated by one space or by none.
`fmt::space` decides which, from the kinds of the two tokens:

| Kind | Tokens |
|---|---|
| `Open` | `(`, except one opening a call, and the `{` of a set literal |
| `Call` | the `(` after a function's, method's or variant's name, opening its parameters or payload, an application's or method call's arguments, or a pattern's binders |
| `Close` | `)`, the `}` of a set literal, and `::*`, which ends a path |
| `Brace` | `{`, except a set literal's |
| `CloseBrace` | `}`, except one closing a `::{` or a set literal |
| `Group` | `::{` |
| `CloseGroup` | the `}` closing a `::{` |
| `Path` | `::`, and `.` reading a field |
| `Comma` | `,` |
| `Colon` | `:` |
| `Negation` | `-` as a unary operator, as in `-1` |
| `Comment` | a comment |
| `Other` | any other token: names, literals, keywords and operators, including `-` as a binary operator |

There is no space after an opening bracket or a unary `-`, and none before a
closing bracket, a separator, a `:` or the `(` of a call. So `x: Int`,
`a::b`, `use a::{b, c}`, `(a or b)`, `f(x, y)`, `f(p).x` and `-1`, but `{ a, b }`, as braces other than
`::{` have spaces inside. Empty braces are written `{}`. A comment always
has a space on both sides, unless it starts or ends the line.

```fren
pub enum Kind { Open, Call, Close, Brace, CloseBrace, Group, CloseGroup, Path, Comma, Colon, Negation, Comment, Other }

use self::Kind::{
    Brace,
    Call,
    Close,
    CloseBrace,
    CloseGroup,
    Colon,
    Comma,
    Comment,
    Group,
    Negation,
    Open,
    Path,
}

pub comp space {
    in before: Kind
    in after: Kind
    pub det out space?

    req comment: when before = Comment or after = Comment, space?
    req empty: when before = Brace and after = CloseBrace, not space?
    req tight: unless before = Comment or after = Comment or (before = Brace and after = CloseBrace),
        space? iff not (before = Open or before = Call or before = Group or before = Path or before = Negation
        or after = Close or after = CloseGroup or after = Path or after = Comma or after = Colon
        or after = Group or after = Call)

    expect binary_operators: when before = Kind::Other and after = Kind::Other, space?
    expect braces_spaced: when before = Brace and after = Kind::Other, space?
    expect groups_tight: when before = Group or after = CloseGroup, space? iff (before = Comment or after = Comment)
    expect calls_tight: when after = Call, space? iff before = Comment
}
```

## Indentation

Each line is indented by four spaces for each brace (`{` or `::{`) that is
open at its start. A line that continues an item, a member or an element
of a list, rather than starting one, is indented by four more:

```text
comp c {
    in mode: Mode
    req r: unless mode = Mode::Off,
        on?
    inst h: heater {
        cold? := true,
    }
}
```

A line that starts with a `|` of a pattern starts its alternative, so
the alternatives of an or-pattern written one per line line up:

```text
match method {
    | Method::Len
    | Method::Card => 0,
    _ => 1,
}
```

A line that starts with a closing brace is indented as the line that
opened it. A comment on a line of its own is indented as the line after
it, but inside the braces when that line closes them. Parentheses do not
add indentation. `fmt::indent` gives the indentation, in spaces:

```fren
pub enum LineStart { Closing, Starting, Continuing }

use self::LineStart::{Closing, Continuing, Starting}

pub comp indent {
    in depth: Int            -- braces open at the start of the line
    in start: LineStart      -- what the line's first token does, or for a comment, the next line's
    in comment?              -- the line is a comment
    pub det out columns: Int

    assume depth_counts: depth >= 0
    assume closes_open: when start = Closing, depth >= 1

    req closing: when start = Closing, columns = 4 * (if comment? then depth else depth - 1)
    req starting: when start = Starting, columns = 4 * depth
    req continuing: when start = Continuing, columns = 4 * depth + 4

    expect non_negative: columns >= 0
    expect comment_inside: when comment?, columns >= 4 * depth
}
```

## Comments at the end of lines

A comment at the end of a line is separated from the code by at least two
spaces. It stays in the column where it starts, if that leaves two spaces,
so comments aligned by hand stay aligned, and a change to one line does not
move the comments of the lines around it. `fmt::comment_column` gives the
column of the comment's `--`, counted from 0:

```fren
pub comp comment_column {
    in width: Int            -- the width of the line's code, with its indentation, after formatting
    in original: Int         -- the column of the comment before formatting
    pub det out column: Int

    assume widths: width >= 0 and original >= 0

    req kept: when original >= width + 2, column = original
    req moved: when original < width + 2, column = width + 2

    expect gap: column >= width + 2
}
```

## Blank lines

At most one blank line separates two lines. There are none at the start of
a file or of a ```` ```fren ```` block, after a line that ends with an
opening brace, or before a line that starts with a closing one. A file
other than a Markdown spec ends with a single newline. `fmt::blank_lines`
gives the number of blank lines kept before a line:

```fren
pub comp blank_lines {
    in blank: Int            -- blank lines before the line in the input
    in first?                -- the line is the first of its file or block
    in after_open?           -- the line before it ends with `{` or `::{`
    in before_close?         -- the line starts with `}`
    pub det out kept: Int

    assume counts: blank >= 0

    req kept_rule: kept = if first? or after_open? or before_close? or blank = 0 then 0 else 1

    expect at_most_one: kept <= 1
    expect never_added: kept <= blank
}
```

## Trailing commas

A list is *vertical* if its closing brace starts a line, or, for the files
of a `tested` claim, which have no brace, if the last file is on a later
line than `tested`. The elements of a vertical list, the bindings of an
instance, the variants of an enumeration, the fields of a record or of a
record literal, the arms of a `match`, the paths of a `use ...::{}` and
the files of a `tested` claim, each end with a comma, including the last;
other lists have no comma after their last element:

```text
inst h: heater { cold?, on? := true }
inst h: heater {
    cold?,
    on? := true,
}
tested h:
    "tests/heater.rs",
    "tests/relay.rs",
```

So an element is added to a vertical list by adding a line. The members of
a component are not a list, and have no commas. `fmt::trailing_comma`
decides whether the last element of a list is followed by a comma:

```fren
pub comp trailing_comma {
    in empty?                -- the list has no elements
    in vertical?
    pub det out comma?

    req empty_list: when empty?, not comma?
    req vertical_list: when not empty? and vertical?, comma?
    req horizontal: when not empty? and not vertical?, not comma?
}
```

## Imports

A *block* of imports is a run of `use` items on consecutive lines. Each
`use` in a block starts its line, ends a line, and shares its lines with no
comment or other token, and is not the item of a `set_option ... in`. Any
other line, including a blank line or a comment, ends the block. So the
imports of a file can be kept in separate blocks, such as one for each
module they come from, and a comment above a `use` stays with it.

Within a block, the formatter rewrites the imports: it collects the paths
they import, with the paths of a `use a::{b, c}` counted as `a::b` and
`a::c`, and writes one `use` for each module prefix, the path without its
last segment. The `use` items are sorted by their paths, segment by
segment, as are the paths in braces. A glob import, `use a::*`, is kept as
it is, after the imports of the same prefix:

```text
use view::Severity::Warning
use check::Verdict
use view::Severity::{Info, Error}
use view::Severity
```

is formatted as

```text
use check::Verdict
use view::Severity
use view::Severity::{Error, Info, Warning}
```

Segments are compared by their characters' code points, so uppercase
before lowercase. `fmt::group_layout` decides how the paths of one module
prefix are written. A `use` with braces is vertical, with one path on each
line, if any of the imports merged into it spanned several lines, or if on
one line it would be wider than 100 columns:

```fren
pub comp group_layout {
    in n_paths: Int          -- paths imported from the prefix
    in was_vertical?         -- some import merged into it spanned several lines
    in fits?                 -- on one line, it is at most 100 columns wide
    pub det out braces?      -- it is written with braces
    pub det out vertical?    -- it is written with one path on each line

    assume some_path: n_paths >= 1

    req braced: braces? iff n_paths > 1
    req vertical_rule: vertical? iff (braces? and (was_vertical? or not fits?))

    expect single: when n_paths = 1, not braces? and not vertical?
    expect stays_vertical: when n_paths > 1 and was_vertical?, vertical?
}
```

`fmt::in_block` decides whether a `use` is part of a block:

```fren
pub comp in_block {
    in alone?                -- it starts and ends its lines, which have no other token and no comment
    in nested?               -- it is the item of a `set_option ... in`
    pub det out sorted?

    req block_rule: sorted? iff (alone? and not nested?)
}
```

## Exit status

| Status | Meaning |
|---|---|
| 0 | every file was formatted, or, with `--check`, already is |
| 1 | with `--check`: some file is not formatted |
| 2 | some file could not be read or parsed, or the arguments are bad |

Without `--check`, each file that parses is rewritten if formatting changes
it, even if another file does not parse. With `--check`, no file is
written. An ignored file is not read. `fmt::file` gives what happens to one
file, and `fmt::exit` the exit status, over the files that are not
ignored:

```fren
pub comp file {
    in check?                -- `--check` was given
    in ignored?              -- the file matches an `--ignore` glob
    in parsed?               -- the file was read, and lexes and parses
    in formatted?            -- formatting it changes nothing
    pub det out written?     -- the file is rewritten
    pub det out diff?        -- a diff is printed

    req write: written? iff (not ignored? and not check? and parsed? and not formatted?)
    req report: diff? iff (not ignored? and check? and parsed? and not formatted?)

    expect check_writes_nothing: when check?, not written?
    expect formatted_untouched: when formatted?, not written? and not diff?
    expect ignored_untouched: when ignored?, not written? and not diff?
}

pub comp exit {
    in check?
    in all_parsed?           -- every file was read, and lexes and parses
    in all_formatted?        -- every file that parses is already formatted
    pub det out code: Int

    req failed: unless all_parsed?, code = 2
    req unformatted: when all_parsed? and check? and not all_formatted?, code = 1
    req formatted: when all_parsed? and (not check? or all_formatted?), code = 0

    expect write_succeeds: when all_parsed? and not check?, code = 0
    expect documented_codes: code >= 0 and code <= 2
}

#fren_check
```
