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
(see [Imports](#imports)). It keeps every comment. It lays out
[lists and blocks](#lists-and-blocks) as rustfmt does: each on one line
if it fits, and otherwise with one element to a line. Elsewhere, for
now, it keeps the line breaks: it breaks no other long line and joins no
other short ones, except to merge imports. On each line, it decides the
indentation and the spaces between tokens; across lines, how many blank
lines separate them. For example,

```text
use climate::Mode::Heat
pub enum Mode {Heat,Cool}
proc   c(
    t:Int,  -- the temperature
): (mode:Mode) {
  ensure r :mode = if t< 18 then Mode::Heat else Mode::Cool
  call h := heater(
      t < 18
  )
}
```

is formatted as

```text
use climate::Mode::Heat
pub enum Mode { Heat, Cool }
proc c(
    t: Int,    -- the temperature
): (mode: Mode) {
    ensure r: mode = if t < 18 then Mode::Heat else Mode::Cool
    call h := heater(t < 18)
}
```

The layout is chosen so that a change to a spec changes as few lines as
possible: adding a member, an import, or an element to a vertical list
that ends with a comma, adds a line, and changes no other line.

A file that cannot be lexed or parsed is not formatted: its error is
reported as `fren check` reports it, and the file is left as it is. Other
static errors, such as an unknown name, do not stop formatting.

## Safety

Formatting keeps the meaning of a file, and what it writes depends only on
what it keeps. A file's *content* is what formatting keeps of it:

- its tokens, but for the trailing commas of lists and the `use` items of
  each [block](#imports) of imports;
- the paths that each block of imports imports, as often, and whether the
  imports of each module prefix span several lines;
- its comments, in order, each with whether it starts its line, and the
  column of one at the end of a line where
  [`fmt::comment_column`](#comments-at-the-end-of-lines) keeps it;
- where it has [blank lines](#blank-lines) that formatting keeps;
- for now, its line breaks but those that a [list or block](#lists-and-blocks)
  decides.

`fmt::format` is what `fren fmt` writes for a file that parses. It writes
`fmt::render` of the file's content, whatever the file's layout: its line
breaks where a list or block decides them, its indentation, its spaces
and its trailing commas. The rendering parses, and has the content it was
rendered from:

```fren
pub type Text                -- the text of a file
pub type Content             -- a file's content

pub fn parses?(Text)
pub fn content(Text): Content

-- What `fren fmt` writes for a file's content.
set_option fren.lint.undecidable "allow" in
pub fn render(c: Content): (r: Text) {
    assume of_a_file: exists (t: Text), parses?(t) and content(t) = c

    ensure parses: parses?(r)
    ensure read_back: content(r) = c
}

-- What `fren fmt` writes for a file.
pub fn format(source: Text): (formatted: Text) {
    assume parses: parses?(source)

    ensure parses_again: parses?(formatted)
    ensure kept: content(formatted) = content(source)
    ensure canonical: formatted = render(content(source))
}
```

So formatting is idempotent, and two files with the same content format
the same, however each is laid out. `fmt::safe` states it of the
formatter, and `fmt::layout_free` of any two files:

```fren
pub proc safe(source: Text): (det formatted: Text) {
    assume parses: parses?(source)

    ensure formats: formatted = format(source)

    expect same_content: content(format(source)) = content(source)
    expect idempotent: format(format(source)) = formatted
}

expect layout_free(p: Text, q: Text) {
    assume parse: parses?(p) and parses?(q)
    assume same_content: content(p) = content(q)

    expect same_format: format(p) = format(q)
}
```

These functions are not interpreted: a proof of what the whole formatter
writes is out of reach, so `fmt::safe` is `tested`. `lake test` formats
every spec in the repository, and each laid out again at random, twice:
with its lists' line breaks and trailing commas changed, wherever no
comment or blank line is near, and its lines indented anew. It checks that
formatting keeps the tokens, imports and comments, with whether each
comment starts its line, that formatting the result again changes
nothing, and that each file laid out again formats as the file does.

The goal is rustfmt's: that a file's content is only its tokens, comments
and blank lines, so that how it was laid out never matters. Two things
are left for later. Line breaks other than those of lists and blocks are
content: those in clauses and in expressions, as between the operands of
an operator, and those in the declarations of enumerations and structs,
in the paths of a `use` and in the files of a `tested` claim. And so is
the column of a comment at the end of a line that is further right than
the formatter would put it, so that comments aligned by hand stay aligned.

## Lists and blocks

A *list* is one of these, each element of which is followed by a comma
but the last:

- the parameters of a procedure or function, and the results of a
  procedure or of a function written with a [block](Lang/Items.md#function-blocks);
- the arguments of a `call`, an application, a method call or a
  refinement;
- the elements of a sequence or set literal, and the members of a
  [Boolean block](Lang/BooleanBlocks.md), `and { ... }`, `or { ... }`,
  `iff { ... }` or `one { ... }`;
- the fields of a record literal or update;
- the arms of a `match` or of a table over a scrutinee, and the rows of
  a table.

`fren fmt` writes each list in one of two ways, as rustfmt does. A
*horizontal* list is on one line, its elements separated by `, `, as in
`f(a, b)` and `P { x := 1, y := 2 }`. A *vertical* list has each element
start a line of its own, indented four spaces more than the line that
opens the list, and its closing bracket start a line, indented as that
line. Each element of a vertical list is followed by a comma, the last
too, except where the syntax allows none after the last: the arguments of
an application or a method call, and the parameters of a function. The fields
of a record update start after its `with`, and the record it updates
stays on the line of its `{`:

```text
call h := heater(cold?, true)
call h := heater(
    cold?,
    true,
)
ensure r: q = { p with
    x := 1,
    y := 2,
}
```

A list with no elements is horizontal. A `match` or a table with arms or
rows is vertical, with one to a line, as rustfmt writes a `match`. Any
other list is horizontal exactly when it fits, that is, when all three
hold:

1. none of its elements must span several lines: none has a line
   comment, a blank line before it, a line break that the formatter keeps,
   or a list in it that would be vertical whatever line it were on;
2. on one line, its elements, separated by `, `, are no wider than the
   table below allows, as rustfmt allows for the like construct; and
3. with the list on one line, that line ends by column 100, rustfmt's
   `max_width`, counting what follows the list up to the first opening
   bracket or the first place where a line may end.

| List | Widest | rustfmt's option |
|---|---|---|
| arguments | 60 | `fn_call_width` |
| parameters and results | 100 | `max_width`, which a function's signature must fit |
| elements of a sequence or set literal, and members of a Boolean block | 60 | `array_width` |
| fields of a record literal or update | 18 | `struct_lit_width` |

These are rustfmt's defaults, those of `use_small_heuristics =
"Default"`. The lists of a file are laid out from the outside in, each on
the lines that the lists around it give, so a list in one that is
horizontal is horizontal too. `fmt::one_line` states the rule:

```fren
pub enum ListKind {
    Arms,                    -- the arms of a `match` or table, or the rows of a table
    Arguments,               -- the arguments of a `call` or a refinement
    ApplicationArguments,    -- the arguments of an application or a method call
    Parameters,              -- the parameters or results of a procedure, or a function's results
    FunctionParameters,      -- the parameters of a function
    Elements,                -- the elements of a sequence or set literal, or the members of a Boolean block
    Fields,                  -- the fields of a record literal or update
}

use self::ListKind::{ApplicationArguments, Arguments, Arms, Elements, Fields, FunctionParameters, Parameters}

-- The widest a list may be on one line, as rustfmt's defaults allow.
pub fn width_limit(list: ListKind): Int := match list {
    Arms => 0,
    Arguments | ApplicationArguments => 60,
    Parameters | FunctionParameters => 100,
    Elements => 60,
    Fields => 18,
}

-- A vertical list's last element is followed by a comma.
pub fn ends_with_comma?(list: ListKind) := not list is ApplicationArguments | FunctionParameters

pub proc one_line(
    list: ListKind,
    n: Int,                  -- its elements
    broken?,                 -- some element must span several lines
    width: Int,              -- the width of its elements on one line, separated by `, `
    line_end: Int,           -- the column where its line would end, with it on one line
): (det vertical?) {
    ensure rule: vertical? iff (n > 0 and (list = Arms or broken? or width > width_limit(list) or line_end > 100))

    expect empty: when n = 0, not vertical?
    expect arms: when n > 0 and list = Arms, vertical?
    expect fits: when n > 0 and list != Arms and not broken? and width <= width_limit(list) and line_end <= 100,
        not vertical?
    expect just_fits: when list = Arguments and n = 2 and not broken? and width = 60 and line_end = 100, not vertical?
    expect just_too_wide: when list = Arguments and n = 2 and width = 61, vertical?
    expect just_too_long: when list = Fields and n = 1 and width = 18 and line_end = 101, vertical?
}
```

`fmt::list_layout` decides it over the elements themselves, each with its
width on one line and whether it must span several lines, from the
column where its first element would start, and the width of what would
follow its last on that line: its closing bracket, with the space before
a brace, and the tokens after it up to where a line may end. Where that
line ends an element of a vertical list, the comma that the list adds
after it counts too. `fmt::list_layout` refines `fmt::one_line`, and the
formatter's decision implements both, proved in Lean:

```fren
-- The elements of a list, each with its width on one line and whether it must span several lines.
pub enum ElementList { Nil, Cons(Int, Bool, ElementList) }

use self::ElementList::{Cons, Nil}

pub fn count(es: ElementList): Int := match es {
    Nil => 0,
    Cons(_, _, rest) => 1 + count(rest),
}

pub fn any_broken?(es: ElementList) := match es {
    Nil => false,
    Cons(_, broken?, rest) => broken? or any_broken?(rest),
}

-- The width of the elements on one line, separated by `, `.
pub fn joined(es: ElementList): Int := match es {
    Nil => 0,
    Cons(w, _, Nil) => w,
    Cons(w, _, rest) => w + 2 + joined(rest),
}

pub proc list_layout(
    list: ListKind,
    elements: ElementList,
    start: Nat,              -- the column where its first element would start
    after: Nat,              -- the width of what would follow its last element on its line
): (det vertical?) {
    ensure rule: vertical? iff (count(elements) > 0 and (list = Arms or any_broken?(elements)
        or joined(elements) > width_limit(list) or start + joined(elements) + after > 100))
}

expect list_layout_one_line(list: ListKind, elements: ElementList, start: Nat, after: Nat) {
    call concrete := list_layout(list, elements, start, after)
    refines concrete one_line(list, count(elements), any_broken?(elements), joined(elements), start + joined(elements) + after)
}
```

## Spaces

Within a line, two tokens are separated by one space or by none.
`fmt::space` decides which, from the kinds of the two tokens:

| Kind | Tokens |
|---|---|
| `Open` | `(`, except one opening a call, and the `{` of a set literal |
| `Call` | the `(` after a function's, method's, variant's or newtype's name, opening its parameters, payload or field, an application's or method call's arguments, a newtype's value, or a variant pattern's patterns; and the `<` that opens a type's arguments or a declaration's type parameters |
| `Close` | `)`, the `}` of a set literal, `::*`, which ends a path, and the `>` that closes a type's arguments or a declaration's type parameters |
| `Brace` | `{`, except a set literal's |
| `CloseBrace` | `}`, except one closing a `::{` or a set literal |
| `Group` | `::{` |
| `CloseGroup` | the `}` closing a `::{` |
| `Path` | `::`, `.` reading a field, and the `..=` or `..` of a range pattern with both bounds, as in `0..=9` |
| `RangeLeading` | the `..=` of a range pattern without a lower bound, as in `..=9` |
| `RangeTrailing` | the `..` of a range pattern without an upper bound, as in `1..` |
| `Comma` | `,` |
| `Colon` | `:` |
| `Negation` | `-` as a unary operator, as in `-1` |
| `Comment` | a comment |
| `Other` | any other token: names, literals, keywords and operators, including `-` as a binary operator, and `<` and `>` as comparisons |

There is no space after an opening bracket or a unary `-`, and none before a
closing bracket, a separator, a `:` or the `(` of a call, nor between a
range's `..=` or `..` and its bounds. So `x: Int`,
`a::b`, `use a::{b, c}`, `(a or b)`, `f(x, y)`, `f(p).x`, `-1`, `-5..=MAX`,
`Option<Set<Int>>` and `fn f<T>(x: T): T`, but `a < b` and `{ a, b }`, as braces other than
`::{` have spaces inside. Empty braces are written `{}`. A comment always
has a space on both sides, unless it starts or ends the line, and so does a
unary `-` before another, `- -1`, since `--` starts a comment.

```fren
pub enum Kind {
    Open, Call, Close, Brace, CloseBrace, Group, CloseGroup, Path, Comma, Colon, Negation, RangeLeading, RangeTrailing, Comment,
    Other,
}

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
    RangeLeading,
    RangeTrailing,
}

pub proc space(before: Kind, after: Kind): (det space?) {
    ensure comment: when before = Comment or after = Comment, space?
    ensure empty: when before = Brace and after = CloseBrace, not space?
    ensure negations: when before = Negation and after = Negation, space?
    ensure tight: unless before = Comment or after = Comment or (before = Brace and after = CloseBrace)
        or (before = Negation and after = Negation),
        space? iff not (before is Open | Call | Group | Path | Negation | RangeLeading
        or after is Close | CloseGroup | Path | Comma | Colon | Group | Call | RangeTrailing)

    expect binary_operators: when before = Kind::Other and after = Kind::Other, space?
    expect braces_spaced: when before = Brace and after = Kind::Other, space?
    expect groups_tight: when before = Group or after = CloseGroup, space? iff (before = Comment or after = Comment)
    expect calls_tight: when after = Call, space? iff before = Comment
}
```

## Indentation

A bracket *indents* if it is a brace, `{` or `::{`, or the opening
bracket of a [list](#lists-and-blocks). A line inside such a bracket is
indented four spaces more than the line that opens the innermost one open
at its start, and a line outside every one is not indented, as rustfmt's
block indentation has it. A line that continues an item, a member or an
element of a list, rather than starting one, is indented by four more:

```text
proc c(mode: Mode) {
    ensure r: unless mode = Mode::Off,
        match mode {
            Mode::Heat => on?,
            _ => not on?,
        }
    call h := heater(
        cold?,
        true,
    )
}
```

A line that starts with a `|` of a `match` arm's pattern, or of a table
arm's, starts its
alternative, so the alternatives of an or-pattern written one per line
line up, and so does a line that starts with the `|` of a
[table](Lang/Expressions.md#tables)'s row, which starts the row. In a [pattern test](Lang/Expressions.md#pattern-tests), such a
line continues its member, as any other line within an expression does:

```text
match method {
    | Method::Len
    | Method::Card => 0,
    _ => 1,
}
ensure sized: sized? iff s is
    | Shape::Circle(_)
    | Shape::Rect(_, _)
```

A member of a function's [block](Lang/Items.md#function-blocks) is
inside its braces, as a procedure's is, so it is indented by four spaces:

```text
fn at(q: Seq<Int>, i: Int): (r: Int) {
    assume in_range: 0 <= i < q.len
    out r := q[i]
}
```

A line that starts with the closing bracket of one that indents is
indented as the line that opens it. A comment on a line of its own is
indented as the line after it, but inside the brackets when that line
closes them. Other brackets, such as those of a grouping or an index, do
not indent. `fmt::indent` gives the indentation, in spaces, from that of
a line that starts an element of the innermost bracket that indents:

```fren
pub enum LineStart { Closing, Starting, Continuing }

use self::LineStart::{Closing, Continuing, Starting}

pub proc indent(
    base: Nat,               -- four more than the line that opens the innermost bracket that indents, or 0 outside every one
    start: LineStart,        -- what the line's first token does, or for a comment, the next line's
    comment?,                -- the line is a comment
): (det columns: Int) {
    assume closes_open: when start = Closing, base >= 4

    ensure closing: when start = Closing, columns = (if comment? then base else base - 4)
    ensure starting: when start = Starting, columns = base
    ensure continuing: when start = Continuing, columns = base + 4

    expect non_negative: columns >= 0
    expect comment_inside: when comment?, columns >= base
}
```

## Comments at the end of lines

A comment at the end of a line is separated from the code by at least two
spaces. It stays in the column where it starts, if that leaves two spaces,
so comments aligned by hand stay aligned, and a change to one line does not
move the comments of the lines around it. `fmt::comment_column` gives the
column of the comment's `--`, counted from 0:

```fren
pub proc comment_column(
    width: Nat,              -- the width of the line's code, with its indentation, after formatting
    original: Nat,           -- the column of the comment before formatting
): (det column: Int) {
    ensure kept: when original >= width + 2, column = original
    ensure moved: when original < width + 2, column = width + 2

    expect gap: column >= width + 2
}
```

## Blank lines

At most one blank line separates two lines. There are none at the start of
a file or of a ```` ```fren ```` block, after a line that ends with a
bracket that [indents](#indentation), or before a line that starts with
its closing bracket. A file
other than a Markdown spec ends with a single newline. `fmt::blank_lines`
gives the number of blank lines kept before a line:

```fren
pub proc blank_lines(
    blank: Nat,              -- blank lines before the line in the input
    first?,                  -- the line is the first of its file or block
    after_open?,             -- the line before it ends with a bracket that indents
    before_close?,           -- the line starts with the closing bracket of one
): (det kept: Int) {
    ensure kept_rule: kept = if first? or after_open? or before_close? or blank = 0 then 0 else 1

    expect at_most_one: kept <= 1
    expect never_added: kept <= blank
}
```

## Trailing commas

Each element of a vertical [list](#lists-and-blocks) is followed by a
comma, the last too, where the syntax allows. So is each element of these
other lists, when they are vertical: the variants of an enumeration, the
fields of a struct and the paths of a `use ...::{}`, each vertical if its
closing brace starts a line, and the files of a `tested` claim, which have
no brace, vertical if the last is on a later line than `tested`. For now,
these other lists keep their line breaks. The last element of a list that
is not vertical has no comma after it:

```text
call h := heater(cold?, true)
call h := heater(
    cold?,
    true,
)
tested h:
    "tests/heater.rs",
    "tests/relay.rs",
```

So an element is added to a vertical list by adding a line. The members of
a procedure are not a list, and have no commas. `fmt::trailing_comma`
decides whether the last element of a list is followed by a comma:

```fren
set_option fren.evidence "enumerated" in
pub proc trailing_comma(
    empty?,                  -- the list has no elements
    vertical?,
    allowed?,                -- the syntax allows a comma after its last element
): (det comma?) {
    ensure empty_list: when empty?, not comma?
    ensure vertical_list: when not empty? and vertical?, comma? iff allowed?
    ensure horizontal: when not empty? and not vertical?, not comma?
}
```

`allowed?` is `fmt::ends_with_comma?` of a list's kind, and holds for the
other lists. The formatter leaves no trailing comma that
[`unnecessary_trailing_comma`](Lint/Pedantic/Text.md#trailing-commas)
reports: the lint fires where no line ends between the comma and the `}`,
`]` or `)`, and the formatter writes the comma only in a vertical list,
whose closing bracket starts a line. `fmt::trailing_comma_lint` states it:

```fren
set_option fren.evidence "enumerated" in
pub proc trailing_comma_lint(
    vertical?,
    allowed?,
) {
    use lint::unnecessary_trailing_comma

    call written := trailing_comma(false, vertical?, allowed?)
    -- Formatted, a line ends before the closing bracket exactly where the list is vertical.
    call reported := unnecessary_trailing_comma(vertical?)

    expect never_reported: when written.comma?, not reported.fires?
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
pub proc group_layout(
    n_paths: Int,            -- paths imported from the prefix
    was_vertical?,           -- some import merged into it spanned several lines
    fits?,                   -- on one line, it is at most 100 columns wide
): (
    det braces?,             -- it is written with braces
    det vertical?,           -- it is written with one path on each line
) {
    assume some_path: n_paths >= 1

    ensure braced: braces? iff n_paths > 1
    ensure vertical_rule: vertical? iff (braces? and (was_vertical? or not fits?))

    expect single: when n_paths = 1, not braces? and not vertical?
    expect stays_vertical: when n_paths > 1 and was_vertical?, vertical?
}
```

`fmt::in_block` decides whether a `use` is part of a block:

```fren
set_option fren.evidence "enumerated" in
pub proc in_block(
    alone?,                  -- it starts and ends its lines, which have no other token and no comment
    nested?,                 -- it is the item of a `set_option ... in`
): (det sorted?) {
    ensure block_rule: sorted? iff (alone? and not nested?)
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
set_option fren.evidence "enumerated" in
pub proc file(
    check?,                  -- `--check` was given
    ignored?,                -- the file matches an `--ignore` glob
    parsed?,                 -- the file was read, and lexes and parses
    formatted?,              -- formatting it changes nothing
): (
    det written?,            -- the file is rewritten
    det diff?,               -- a diff is printed
) {
    ensure write: written? iff (not ignored? and not check? and parsed? and not formatted?)
    ensure report: diff? iff (not ignored? and check? and parsed? and not formatted?)

    expect check_writes_nothing: when check?, not written?
    expect formatted_untouched: when formatted?, not written? and not diff?
    expect ignored_untouched: when ignored?, not written? and not diff?
}

pub proc exit(
    check?,
    all_parsed?,             -- every file was read, and lexes and parses
    all_formatted?,          -- every file that parses is already formatted
): (det code: Int) {
    ensure failed: unless all_parsed?, code = 2
    ensure unformatted: when all_parsed? and check? and not all_formatted?, code = 1
    ensure formatted: when all_parsed? and (not check? or all_formatted?), code = 0

    expect write_succeeds: when all_parsed? and not check?, code = 0
    expect documented_codes: 0 <= code <= 2
}
```

`fmt::exit` follows the convention of every command,
[`cli::exit_status`](Cli.md#exit-status), with `fren fmt` able to run
exactly when every file parses:

```fren
use cli::exit_status

expect fmt_exit_status(check?, all_parsed?, all_formatted?) {
    call concrete := exit(check?, all_parsed?, all_formatted?)
    refines concrete exit_status((all_parsed?))
}

#fren_check
```
