# Formatting

```
fren fmt [--check] [--ignore GLOB]... FILE...
```

`fren fmt` rewrites spec files in Fren's standard layout. With `--check`,
it changes nothing, and instead prints what it would change, as a diff on
standard output. With `--ignore GLOB`, it skips the files that match the
glob, as if they were not given, so that a list of files, such as every
spec in a repository, can leave out some that are deliberately not
formatted. `*` matches within a path segment, and `**` any number of
segments, as for [`fren trace --tests`](Trace.md). A file whose name ends
in `.md` is a [Markdown spec](Markdown.md): its ```` ```fren ```` blocks
are read together, as `fren check` reads them, but each is laid out as if
it started a file, and everything else is kept as it is. Any other file is
read as Fren source.

```fren
pub mod fmt
```

The formatter changes whitespace, the commas at the end of lists (see
[Trailing commas](#trailing-commas)), and the order and grouping of
imports (see [Imports](#imports)). It keeps every comment. It lays out
[lists and blocks](#lists-and-blocks) as rustfmt does: each on one line if
it fits, and otherwise with one element to a line, but the arms of a
`match` or a table and the rows of a table always one to a line, and the
members of a procedure's, function's or global expectation's block one to
a line unless there is just one that fits. It puts the [right
side](#right-sides) of a `:=` or `=>` on the operator's line if it fits
there, or if it is a whole `match`, table, call, literal or other
bracketed expression whose line fits up to its bracket, which then breaks,
or an expression that the author broke by hand there, and otherwise on the
next line, indented. It breaks a [chain](#chains) of operators that does
not fit on its line before each of its operators, as rustfmt breaks a
binary expression, and puts the expression of a clause, such as
`ensure r:`, on the next line where it is a chain that breaks on the
clause's line. Elsewhere, for now, it keeps the line breaks: it breaks
no other long line and joins no other short ones, except to merge imports.
On each line, it decides the indentation and the spaces between tokens;
across lines, how many blank lines separate them. For example,

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
    t: Int,  -- the temperature
): (mode: Mode) {
    ensure r: mode = if t < 18 then Mode::Heat else Mode::Cool
    call h := heater(t < 18)
}
```

## Principles

Layout questions are decided from these principles (#546). Where two
conflict, the Reqs that cite them say which wins: an `if` that spans
several lines, for example, moves to the next line even where it does not
fit there on one line, so that each `else` lines up with its `if`, unless
the author broke it by hand only before its `then` or within its
condition, which principle 6 keeps.

1. **If it fits on one line, use one line**: [lists and blocks](#lists-and-blocks)
   (`fmt::one_line`, `fmt::list_layout`) and [right sides](#right-sides)
   (`fmt::right_side`'s `fits_here?`).
2. **Otherwise, prefer the layout with fewer lines and less nesting.** A
   right side moves to the next line only if it then fits there on one line
   (`fmt::right_side`'s `fits_next?`), as rustfmt's assignment rule has it.
3. **Indentation shows structure.** A continuation is indented past the
   start of what it continues, and a closing bracket lines up with the
   line that opened what it closes (`fmt::indent`, `fmt::right_side`).
   Formatting must not mislead.
4. **Hug only a whole unit.** A bracketed construct, such as a call, a
   literal, a `match` or a table, hangs on its opener's line only when it
   is the whole right side (`fmt::right_side`'s `overflows?`) or the sole
   or last argument (not yet: a call's sole argument is made vertical, see
   [Safety](#safety)). So, following from principles 3 and 4, after a
   signature that spans several lines a whole unit hugs as anywhere, and
   anything else starts the next line.
5. **Break before operators**, with continuations one level in: a
   [chain](#chains) that does not fit on its line breaks before each of
   its operators, the loosest first, and each line that starts with one of
   them is indented four spaces past the line it continues
   (`fmt::chain_layout`). So the expression of a clause that breaks starts
   the next line, and its operators are indented under it
   (`fmt::right_side`'s `breaks?`). One shape breaks *after* its operator:
   a single short name before `iff` or `=`, as in `ensure rule: noted? iff`,
   whose right operand then starts the next line, one level in
   (`fmt::chain_side`). A call after an operator that would not fit on a
   line of its own anyway hugs it rather than the chain breaking, as in
   `lhs = f(` (`fmt::hugs?`).
6. **Leave a choice to the author only where no rule decides it well**:
   the line breaks of a chain that is not its line's expression, such as a
   guard's condition before its body (`fmt::chain_kept`), the other line
   breaks of an expression broken by hand (`fmt::right_side`'s `chained?`
   and `written?`), and the column of a comment aligned by hand
   (`fmt::comment_column`). This makes an exception to principle 3: where
   an expression broken by hand outside its brackets moves to the next
   line, its links line up with its first line, as written, rather than
   being indented past it.

The layout is chosen so that a change to a spec changes as few lines as
possible: adding a member, an import, or an element to a vertical list
that ends with a comma, adds a line, and changes no other line.

A file that cannot be lexed or parsed is not formatted: its error is
reported as `fren check` reports it, and the file is left as it is. Other
static errors, such as an unknown name, do not stop formatting.

## Safety

Formatting keeps the meaning of a file, and what it writes depends only on
what it keeps. A file's *content* is what formatting keeps of it:

- its tokens and comments, in order, but for the trailing commas of lists
  and of `tested` claims and the `use` items of each [block](#imports) of
  imports, a comma before a line break, a line comment or a block comment
  that starts its line counting as one after it
  ([`fmt::order`](#commas-and-comments));
- the paths that each block of imports imports, as often, and whether the
  imports of each module prefix span several lines;
- whether each comment starts its line, and the column of one at the end
  of a line where [`fmt::comment_column`](#comments-at-the-end-of-lines)
  keeps it;
- where it has [blank lines](#blank-lines) that formatting keeps: those
  that `fmt::blank_lines` keeps before a line, but not those in a gap that
  a list or block joins onto one line, such as one before a block's `{`
  ([`fmt::line_break`](#lists-and-blocks)), nor those before a line that
  `fmt::apart` sets apart from the item before it, which always has one;
- for now, its line breaks but those that a [list or block](#lists-and-blocks)
  decides, such as those between the members of a procedure and the one
  before a block's `{`, those before the [right side](#right-sides) of a
  `:=` or `=>`, or of a clause's `:`, but an expression broken by hand, and
  those before and after the operators of a [chain](#chains) that the
  formatter lays out, a line break before a
  [comma](#commas-and-comments) counting as one after it.

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
writes is out of reach, so `fmt::safe` is `tested`, by the `lake test` job
that checks formatting, which also checks `fmt::layout_free`. A claim
names a procedure, and `fmt::layout_free` is an expectation, so its trust
is recorded only here, as that of `fmt::safe`. The job formats every spec
in the repository, and each laid out again at random, twice. Laying out
again changes the line breaks of lists and blocks, the one before a
block's `{` included, and their trailing commas, the line breaks before
right sides and around the operators of the chains that the formatter lays
out, the side of a comma that a line break or a line comment is
on, the spaces between tokens and the indentation of lines. It reaches the
gaps of lists and blocks with blank lines too: one whose blank lines go
(`fmt::line_break`) gets a space, a line break or a blank line, whatever
it had, and one between two elements or members keeps its blank lines,
with spaces on them. The gap before a line that `fmt::apart` sets apart,
as formatted, with no comment in it or on its lines, gets a line break or
a blank line, whatever it had. Other than moving a comma past a line
comment, which keeps the comment's column, it leaves alone the lines with
comments, and the gaps between two tokens with no space, where a space
could change what the parser reads, as in `f(x)`. It changes no part of a
file's content. The job checks that formatting keeps the order of the
tokens and comments, computed by the implementation of `fmt::ordering`,
with whether each comment starts its line, and the imports; that no comma
of what it writes, trailing ones and those of `use` items included,
follows a line break, a line comment or a block comment that starts its
line; that its blank lines are those that formatting keeps: before each
line it writes, what `fmt::blank_lines` keeps of the source's, with
whether `fmt::apart` sets the line apart, computed from what it writes,
and a blank line lost to a joined line only in a gap whose blank lines
`fmt::line_break` drops, but for the lines after a `use` item, as imports
are merged and sorted; that formatting the result again changes nothing;
and that each file laid out again formats as the file does. It does not
check that formatting keeps the rest of the content: the columns of
comments, and whether imports span several lines.

The goal is rustfmt's: that a file's content is only its tokens, comments
and blank lines, so that how it was laid out never matters, and that
`fren fmt` writes what rustfmt would write for the like Rust. These things
are left for later:

- Line breaks other than those of lists and blocks, those before right
  sides and those around the operators of chains are content: those in
  clauses and in expressions, as after a guard's comma or before an `if`'s
  `else`, or between the operands of a chain that is not its line's
  expression, and those in the declarations of enumerations and structs,
  in the paths of a `use` and in the files of a `tested` claim. rustfmt
  breaks a long expression wherever it may; `fren fmt` breaks only chains
  that are their line's expression, and keeps a list in another expression
  on one line (rule 3 of [Lists and blocks](#lists-and-blocks)).
- The column of a comment at the end of a line that is further right than
  the formatter would put it is content, so that comments aligned by hand
  stay aligned.
- rustfmt keeps a call's sole argument that is a call, a `match`, a
  record or a sequence on the call's line and breaks only inside it, as
  in `f(match x {` ... `})`. `fren fmt` makes the arguments vertical.
- rustfmt puts a long sequence of short literals several to a line
  (`short_array_element_width_threshold`). `fren fmt` puts one to a line.
- The test fixtures in `fmtPending` are not formatted yet (#509).

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

The members of a procedure's block, of a [function's
block](Lang/Items.md#function-blocks) and of a [global
expectation](Lang/Global.md)'s block are laid out as a list too, a
*block*, but they are separated by line breaks rather than commas. A
Boolean block, whose members are separated by commas, is a list, not a
block in this sense, and neither is a [block of imports](#imports). An
[evidence setting](Evidence.md), `set_option fren.evidence "..." in`, is
not separated from the member after it.

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

A block's `{` goes on the line of what comes before it, unless a line
comment ends that line, as rustfmt puts a function's `{` on the line of
its signature. So `proc c(x: Int): (y: Int)`, then `{` on the next line,
is written `proc c(x: Int): (y: Int) {`, and a blank line before the `{`
goes with the line break, as rustfmt drops it. `fmt::line_break` says
where a list or block ends a line: where it is vertical, after its
opening bracket, between its elements and before its closing bracket, and
elsewhere only where a line must end whatever the layout: after a line
comment, before a comment that starts its line, between two blocks of a
Markdown spec, and at a blank line between two elements or members, which
keeps them on lines of their own. The blank lines of any other gap that a
list or block decides go where the gap has no line break, and are not
kept after an opening bracket or before a closing one where it has one
([Blank lines](#blank-lines)). The formatter's decision implements it,
proved in Lean:

```fren
-- A gap between two pieces whose line break a list or block decides.
pub enum Gap {
    AfterOpen,               -- after its opening bracket
    AfterComma,              -- before an element or member that follows another
    BeforeClose,             -- before its closing bracket
    UpdatedRecord,           -- after a record update's `{`, before the record it updates
    BlockBrace,              -- before a block's `{`
    RightSide,               -- after a `:=` or `=>`, before its right side (`fmt::right_side`)
    Operator,                -- before an operator of a chain that the formatter lays out (`fmt::chain_layout`)
    AfterOperator,           -- after such an operator, where it breaks after it (`fmt::chain_side`)
}

-- A line must end at the gap whatever the layout.
pub fn forced?(gap: Gap, blank: Nat, boundary?, after_line_comment?, comment_follows?) :=
    boundary? or after_line_comment? or comment_follows? or (gap = Gap::AfterComma and blank > 0)

pub proc line_break(
    gap: Gap,
    vertical?,               -- the list or block is vertical, or the right side starts the next line
    blank: Nat,              -- the blank lines in the gap
    boundary?,               -- the gap is between two blocks of a Markdown spec
    after_line_comment?,     -- a line comment ends the line before the gap
    comment_follows?,        -- a comment that starts its line follows the gap
): (det break?) {
    ensure rule: break? iff
        (forced?(gap, blank, boundary?, after_line_comment?, comment_follows?)
            or (vertical?
                and gap is Gap::AfterOpen | Gap::AfterComma | Gap::BeforeClose | Gap::RightSide | Gap::Operator
                    | Gap::AfterOperator))

    -- `{ p with` and `) {` stay on their lines, blank lines or not.
    expect joined: when gap is Gap::UpdatedRecord | Gap::BlockBrace and not boundary?
        and not after_line_comment? and not comment_follows?, not break?
    -- A blank line between two elements or members keeps them on lines of their own.
    expect blank_between: when gap = Gap::AfterComma and blank > 0, break?
    -- `:= x + 1` stays on its line, blank lines or not, where it fits.
    expect right_side_joined: when gap = Gap::RightSide and not vertical? and not boundary?
        and not after_line_comment? and not comment_follows?, not break?
    -- `a and` `b`: a line ends after an operator only where its chain breaks there.
    expect operator_joined: when gap = Gap::AfterOperator and not vertical? and not boundary?
        and not after_line_comment? and not comment_follows?, not break?
}
```

A list with no elements is horizontal, as in `proc c() {}`. A `match`
or a table with arms or rows is vertical, with one to a line, as rustfmt
writes a `match`. So is a block with two or more members, with one
member to a line, as rustfmt writes a function's body. A block with one
member is a list like the others below: it is horizontal when it fits,
as rustfmt writes a function whose body is one expression when its
`fn_single_line` is `true`, and it fits only on a line that ends by
column 100, as a function's whole line must. So a procedure written
vertically with one short member

```text
proc c(m: Mode): (on?) {
    ensure r: on? iff m = Mode::Heat
}
```

is joined onto one line, and one written so already stays as it is:

```text
proc c(m: Mode): (on?) { ensure r: on? iff m = Mode::Heat }
```

A block's single member that must span several lines, such as a `match`
or a table with arms, or a member with a line comment, keeps the block
vertical, as does one that would end its line past column 100, however
long the line is before the block: unlike the elements of other lists,
the member moves to a line of its own, which is shorter. A comment after
the block's `}` on its line counts towards column 100 too, as joining
would bring it onto the block's line. A signature that spans several
lines keeps the block vertical as well, as rustfmt puts a function on
one line only if all of it fits there: a block joins only the line that
starts its item ([`fmt::continued`](#a-blocks-line)). So it never joins a
line such as `): (y: Int) {`.

Any other list is horizontal exactly when it fits, that is, when all
three hold:

1. none of its elements must span several lines: none has a line
   comment, a blank line before it, a line break that the formatter keeps,
   or a list in it that would be vertical whatever line it were on;
2. on one line, its elements, separated by `, `, are no wider than the
   table below allows, as rustfmt allows for the like construct; and
3. with the list on one line, that line ends by column 100, rustfmt's
   `max_width`, counting what follows the list up to the next place
   where a line may end: after a bracket that indents, before a comment
   or a line break that the formatter keeps, or where a list around it
   may break. What follows a signature's parameters or results counts
   only up to and including the `:=` before a function's body, if it
   gets that far, as rustfmt counts a signature only up to its ` {`.
   This counts only where breaking the list shortens the line, so that
   the line up to its first element ends by column 100, and only where
   the list *is its line's expression*: either it is a procedure's or
   function's parameters or results, as rustfmt breaks a long signature
   there first, or a block, or both of these hold:
   - what follows its closing bracket on the line, as far as it counts,
     is only closing brackets, commas, `=>`, the `>` that closes a
     type's arguments, and a bracket that indents; and
   - in each expression that holds it and starts on its line, at most 4
     columns come before its *head*, the names, `::` and `.` just before
     its opening bracket. A line that continues an expression from the
     line before starts one, after its operator, if it starts with one:
     the innermost operation that starts there and holds the list, if
     any.
     A record literal or update is exempt from the operation of a binary
     operator whose whole right operand it is, and only from that one.

   Otherwise the list is horizontal when 1 and 2 hold, however long its
   line, but for a record wider than 18 columns, as below.

A list that is not its line's expression is an operand, as `f(a)` and
`g(b)` are in `x and f(a) = g(b)`, a branch, as in `if c then f(a) else
g(b)`, or the body of a guard or a quantifier, or it is followed by a
method or a field, as in `f(a).len`. Breaking it would leave the rest of
the expression on the lines of its brackets, which are no shorter.
rustfmt breaks the expression instead, between its operands, and gives
each list the line that is left. It keeps a right operand on the line
of its operator, and breaks it in place, only where the left operand is
at most 4 wide, as in `r = f(` ..., or the operand's first line ends with
a brace, as for a struct literal in `q = P {` .... A chain of operators,
as in `a and b and q = P {`, it breaks one operand to a line whatever
its operands. `fren fmt` allows the same, a little more strictly, as it
counts all that comes before the list in the expression, and exempts
from that only the operation whose whole right operand a record is. A
set literal is not exempt: it is Rust's array, which opens with `[`, and
so are a Boolean block's members. Until `fren fmt` breaks expressions,
every other such list stays on one line.

A record literal or update whose fields are wider than 18 columns,
rustfmt's `struct_lit_width`, is a *wide record* (`fmt::wide_record?`). A
wide record, or a list that holds one at any depth, such as a call's
arguments or a sequence's elements, is vertical where its line would end
past column 100 with all that follows it on that line, wherever it is,
even where a field or a method follows it. Where such a list is vertical
only for the wide records it holds, every list in it that holds one is
vertical too (`fmt::wide_within`).

> **Rationale:** records may be 40 wide, where rustfmt's 18 split some of
> a run of short literals that read alike and not others (#546). Wide
> records stay vertical where their line is too long, as rustfmt's 18
> would have them, so that the wider limit only joins records whose lines
> fit.

| List | Widest | rustfmt's option |
|---|---|---|
| arguments | 60 | `fn_call_width` |
| parameters and results | 100 | `max_width`, which a function's signature must fit |
| elements of a sequence or set literal, and members of a Boolean block | 60 | `array_width` |
| fields of a record literal or update | 40 | `struct_lit_width`, which is 18 by default |
| a block's single member | 100 | `max_width`, which a function on one line must fit |

These are rustfmt's defaults, those of `use_small_heuristics = "Default"`,
but for a record's fields. rustfmt's 18 columns split some of a run of
short record literals that read alike and not others, as each list is laid
out on its own, so `fren fmt` allows 40 (#546). The lists of a file are
laid out from the outside in, each on the lines that the lists around it
give, so a list in one that is horizontal is horizontal too. Otherwise
each list is laid out on its own: `fmt::list_layout` decides it from its
own elements and line, as rustfmt lays out each, and two lists that look
alike may be laid out differently. So of the arms of one `match`, only one
whose call is too wide breaks it, and of two record literals alike, only
one too wide is vertical (`test/cli/fmt/independent.fren`):

```text
ensure r1: r = match n {
    0 => wrap(n),
    _ => wrap(
        wrap(n + 1000000000 + m) + wrap(n + 2000000000 + m) + wrap(3)
    ),
}
ensure r2: p = P { x := n + 1000000000, y := m + 2000000000 }
ensure r3: q = P {
    x := n + 10000000000,
    y := m + 2000000000,
}
```

`fmt::one_line` states the rule:

```fren
pub enum ListKind {
    Arms,                    -- the arms of a `match` or table, or the rows of a table
    Arguments,               -- the arguments of a `call` or a refinement
    ApplicationArguments,    -- the arguments of an application or a method call
    Parameters,              -- the parameters or results of a procedure, or a function's results
    FunctionParameters,      -- the parameters of a function
    Elements,                -- the elements of a sequence or set literal, or the members of a Boolean block
    Fields,                  -- the fields of a record literal or update
    Members,                 -- the members of a procedure's, function's or global expectation's block
}

use self::ListKind::{
    ApplicationArguments,
    Arguments,
    Arms,
    Elements,
    Fields,
    FunctionParameters,
    Members,
    Parameters,
}

-- The lists that are vertical whenever they have elements: a `match`'s or a table's.
pub fn always_vertical?(list: ListKind) := list = Arms

-- A block is on one line only with one member, only on the line that starts its item, and only
-- if that line ends by column 100, as rustfmt puts a function on one line only if all of it fits
-- there.
pub fn stacked?(list: ListKind, n: Int, continued?, line_end: Int) :=
    list = Members and (n > 1 or continued? or line_end > 100)

-- The widest a list may be on one line, as rustfmt's defaults allow, but for a record's fields.
pub fn width_limit(list: ListKind): Int := match list {
    Arms => 0,
    Arguments | ApplicationArguments => 60,
    Parameters | FunctionParameters | Members => 100,
    Elements => 60,
    Fields => 40,
}

-- A wide record: one whose fields are wider than rustfmt's `struct_lit_width` of 18.
pub fn wide_record?(list: ListKind, width: Int) := list = Fields and width > 18

-- A vertical list's last element is followed by a comma.
pub fn ends_with_comma?(list: ListKind) :=
    not list is ApplicationArguments | FunctionParameters | Members

pub proc one_line(
    list: ListKind,
    n: Int,                  -- its elements
    broken?,                 -- some element must span several lines
    wide?,                   -- it is a record wider than 18, or holds one (`fmt::list_layout`)
    width: Int,              -- the width of its elements on one line, separated by `, `
    start: Int,              -- the column where its first element would start
    line_end: Int,           -- the column where its line would end, with it on one line
    rest_end: Int,           -- where its line would end, with all that follows it on one line
    own_line?,               -- it is its line's expression (`fmt::own_line`)
    continued?,              -- its line continues an item from an earlier line
    within?,                 -- a list around it is vertical only for its wide records (`fmt::wide_within`)
): (det vertical?) {
    ensure rule: vertical? iff
        (n > 0
            and (always_vertical?(list)
                or stacked?(list, n, continued?, line_end)
                or broken?
                or width > width_limit(list)
                or (own_line? and start <= 100 < line_end)
                or (wide? and (rest_end > 100 or within?))))

    expect empty: when n = 0, not vertical?
    expect arms: when n > 0 and list = Arms, vertical?
    -- A block's members are one to a line when it has two or more, however short.
    expect members: when n > 1 and list = Members, vertical?
    -- A block with one short member is on one line.
    expect single_member: when list = Members and n = 1 and not continued? and not broken? and not wide?
        and width <= 100 and line_end <= 100, not vertical?
    -- `): (y: Int) {`: a block after a signature that spans several lines is vertical.
    expect after_long_signature: when list = Members and n > 0 and continued?, vertical?
    -- A block's single member that must span several lines keeps the block vertical.
    expect broken_member: when list = Members and n = 1 and broken?, vertical?
    -- A block whose line would end past column 100 is vertical.
    expect long_member: when list = Members and n = 1 and line_end > 100, vertical?
    expect fits: when n > 0 and not always_vertical?(list)
        and not stacked?(list, n, continued?, line_end) and not broken?
        and width <= width_limit(list) and line_end <= 100 and not (wide? and (rest_end > 100 or within?)),
        not vertical?
    expect just_fits: when list = Arguments and n = 2 and not broken? and not wide? and width = 60 and line_end = 100,
        not vertical?
    expect just_too_wide: when list = Arguments and n = 2 and width = 61, vertical?
    -- A record's fields fit in 40 columns, where rustfmt's default is 18 (#546).
    expect fields_just_fit: when list = Fields and n = 2 and not broken? and width = 40 and line_end = 100
        and rest_end = 100 and not within?, not vertical?
    expect fields_just_too_wide: when list = Fields and n = 2 and width = 41, vertical?
    -- A record wider than 18, or a list that holds one, is vertical where its line, with all that
    -- follows it, is too long, wherever it is; any other list is held to its line's expression.
    expect wide_long_line: when n > 0 and wide? and rest_end = 101, vertical?
    -- Inside a list that is vertical only for its wide records, it is vertical too.
    expect wide_within_vertical: when n > 0 and wide? and within?, vertical?
    expect narrow_operand: when list = Fields and n = 2 and not broken? and not wide? and width = 18
        and not own_line? and not continued?, not vertical?
    expect just_too_long: when list = Fields and n = 1 and width = 18 and start = 80 and line_end = 101 and own_line?,
        vertical?
    -- Breaking a list helps its line only where the list is the line's expression: elsewhere, the
    -- rest of the expression would still be on the lines of its brackets.
    expect operand: when not own_line? and not always_vertical?(list)
        and not stacked?(list, n, continued?, line_end) and not broken?
        and width <= width_limit(list) and not (wide? and (rest_end > 100 or within?)), not vertical?
    -- A list that is vertical for its line's length alone shortens the line: the line fits up to its
    -- first element, and is too long with the list on it.
    expect helps: when vertical? and not always_vertical?(list)
        and not stacked?(list, n, continued?, line_end) and not broken?
        and width <= width_limit(list) and not wide?, own_line? and start <= 100 < line_end
}
```

`fmt::list_layout` decides it over the elements themselves, each with its
width on one line, whether it must span several lines and whether it holds
a list that `fmt::wide_list` finds wide, from the column where its first
element would start, and the width of what would follow its last on that
line: its closing bracket, with the space before a brace, and the tokens
after it up to where a line may end. Where that line ends an element of a
vertical list, the comma that the list adds after it counts too. After a
block's `}`, a comment on its line counts too, with the two spaces before
it. For a list that `fmt::wide_list` finds wide, all that follows its last
element counts as well, as `rest`, with every list after it on one line,
up to a comment or a line break that formatting keeps or that a list or
right side around it decides: it decides only the clause for wide lists,
and the line's end by `after` still decides the others. Whether the list
is its line's expression is decided by
[`fmt::own_line`](#a-lists-own-line), whether its line continues an item
by [`fmt::continued`](#a-blocks-line), and whether a list around it is
vertical only for its wide records by `fmt::wide_within`, from the outside
in. `fmt::list_layout` refines `fmt::one_line`, and the formatter's
decisions implement them, proved in Lean:

```fren
-- The elements of a list, each with its width on one line, whether it must span several lines,
-- and whether it holds a list that is a record wider than 18 or holds one (`list_layout`'s `wide?`).
pub enum ElementList { Nil, Cons(Int, Bool, Bool, ElementList) }

use self::ElementList::{Cons, Nil}

pub fn count(es: ElementList): Int := match es {
    Nil => 0,
    Cons(_, _, _, rest) => 1 + count(rest),
}

pub fn any_broken?(es: ElementList) := match es {
    Nil => false,
    Cons(_, broken?, _, rest) => broken? or any_broken?(rest),
}

pub fn any_wide?(es: ElementList) := match es {
    Nil => false,
    Cons(_, _, wide?, rest) => wide? or any_wide?(rest),
}

-- The width of the elements on one line, separated by `, `.
pub fn joined(es: ElementList): Int := match es {
    Nil => 0,
    Cons(w, _, _, Nil) => w,
    Cons(w, _, _, rest) => w + 2 + joined(rest),
}

-- It is a record wider than 18, or an element holds one, at any depth.
pub fn holds_wide?(list: ListKind, es: ElementList) :=
    wide_record?(list, joined(es)) or any_wide?(es)

-- Whether a list is a record wider than 18, or holds one, which an element of the list around it
-- then holds.
pub proc wide_list(list: ListKind, elements: ElementList): (det wide?) {
    ensure rule: wide? iff holds_wide?(list, elements)
}

-- It is vertical for the rule but its wide records, its line ending at `line_end`.
pub fn base_vertical?(
    list: ListKind,
    elements: ElementList,
    start: Nat,
    line_end: Int,
    own_line?,
    continued?
) :=
    count(elements) > 0
        and (always_vertical?(list)
            or stacked?(list, count(elements), continued?, line_end)
            or any_broken?(elements)
            or joined(elements) > width_limit(list)
            or (own_line? and start <= 100 < line_end))

pub proc list_layout(
    list: ListKind,
    elements: ElementList,
    start: Nat,              -- the column where its first element would start
    after: Nat,              -- the width of what would follow its last element on its line
    rest: Nat,               -- the width of all that follows its last element, to a kept line break
    own_line?,               -- it is its line's expression (`fmt::own_line`)
    continued?,              -- its line continues an item from an earlier line
    within?,                 -- a list around it is vertical only for its wide records
): (det vertical?) {
    let line_end: Int := start + joined(elements) + after
    let rest_end: Int := start + joined(elements) + rest
    ensure rule: vertical? iff
        (base_vertical?(list, elements, start, line_end, own_line?, continued?)
            or (count(elements) > 0
                and holds_wide?(list, elements)
                and (rest_end > 100 or within?)))
}

-- Whether the lists inside a list are inside one that is vertical only for its wide records: one
-- around them is, or it is, as its line is too long with them on it, and it would not be vertical
-- but for them.
pub proc wide_within(
    list: ListKind,
    elements: ElementList,
    start: Nat,
    after: Nat,
    rest: Nat,
    own_line?,
    continued?,
    within?,                 -- a list around it is vertical only for its wide records
): (det inner?) {
    let line_end: Int := start + joined(elements) + after
    let rest_end: Int := start + joined(elements) + rest
    ensure rule: inner? iff
        (within?
            or (holds_wide?(list, elements)
                and rest_end > 100
                and not base_vertical?(list, elements, start, line_end, own_line?, continued?)))
}

expect list_layout_one_line(
    list: ListKind,
    elements: ElementList,
    start: Nat,
    after: Nat,
    rest: Nat,
    own_line?,
    continued?,
    within?,
) {
    call concrete := list_layout(
        list,
        elements,
        start,
        after,
        rest,
        own_line?,
        continued?,
        within?,
    )
    refines concrete one_line(
        list,
        count(elements),
        any_broken?(elements),
        holds_wide?(list, elements),
        joined(elements),
        start,
        start + joined(elements) + after,
        start + joined(elements) + rest,
        own_line?,
        continued?,
        within?,
    )
}
```

### A block's line

`fmt::continued` decides whether the line of a block continues an item
from an earlier line, for the block's layout. It does unless the line's
first token starts an item that the block is in: its procedure, function
or global expectation, or a `set_option ... in` before it, which starts
an item that holds that one. So a block whose item's signature spans
several lines is on a line that continues it, such as `): (y: Int) {` or
`: (y: Int) {`, and so is a block whose `{` starts its line, after a line
comment. Such a block stays vertical however short its member, as rustfmt
puts a function on one line only if all of it fits on one line, and the
line comment keeps the signature's line from taking the block. The parser
gives the first tokens of the items that each block is in, and the
formatter's decision implements `fmt::continued`, proved in Lean, and
gives what it decides to `fmt::list_layout`:

```fren
-- Indices of tokens.
pub enum Indices { Nil, Index(Int, Indices) }

use self::Indices::Index

-- Whether `i` is one of `indices`.
pub fn has?(indices: Indices, i: Int) := match indices {
    Indices::Nil => false,
    Index(j, rest) => j = i or has?(rest, i),
}

pub proc continued(
    tokens?,                 -- the line has a token before the block's `{`
    first: Int,              -- the index of the line's first token
    items: Indices,          -- the indices of the first tokens of the items that the block is in
): (det continued?) {
    -- A block joins only the line that starts its item.
    ensure rule: continued? iff not (tokens? and has?(items, first))

    expect brace_first: when not tokens?, continued?
    expect outside_items: when not has?(items, first), continued?
}
```

### A list's own line

`fmt::own_line` decides whether a list is its line's expression, for
rule 3. It decides from the tokens that follow the list's closing bracket
on its line, as far as they count, and from the expressions that hold the
list and start on its line. Each expression comes with the columns before
the list's head in it, and, where it is the operation of a binary
operator, the span of its right operand, as the parser reads it. Spans are
offsets in the file: a right operand is the whole list where it starts at
the list's head and ends with its closing bracket. The expression that a
continued line starts, after its operator, is the innermost operation that
starts there and holds the list, with that operation's right operand. The
formatter's decision implements `fmt::own_line`, proved in Lean, and gives
what it decides to `fmt::list_layout`:

```fren
-- A token that follows a list's closing bracket on its line.
pub enum Follower {
    Closing,                 -- `)`, `]` or `}`
    Comma,                   -- `,`
    Arrow,                   -- `=>`
    TypeClosing,             -- the `>` that closes a type's arguments
    Opening,                 -- a bracket that indents
    Other,                   -- any other token
}

pub enum Followers { Nil, Then(Follower, Followers) }

-- The right operand of an expression that holds a list: none, where the expression is not the
-- operation of a binary operator, or where it starts and ends.
pub enum Operand { Absent, Spans(Int, Int) }

-- The expressions that hold a list and start on its line, each with the columns before the list's
-- head in it, and its right operand.
pub enum Holders { Nil, Holder(Int, Operand, Holders) }

use self::Followers::Then
use self::Holders::Holder
use self::Operand::{Absent, Spans}

-- Only closing brackets, commas, `=>`, a type's `>` and brackets that indent follow.
pub fn only_closing?(followers: Followers) := match followers {
    Followers::Nil => true,
    Then(token, rest) => token != Follower::Other and only_closing?(rest),
}

-- The list, from `head` to `close`, is the whole of a right operand.
pub fn whole?(operand: Operand, head: Int, close: Int) := match operand {
    Absent => false,
    Spans(start, stop) => start = head and stop = close,
}

-- In each expression that holds the list, at most 4 columns come before its head, but where the
-- list is a record that is the expression's whole right operand.
pub fn heads_near?(list: ListKind, head: Int, close: Int, holders: Holders) := match holders {
    Holders::Nil => true,
    Holder(columns, operand, rest) =>
        (columns <= 4 or (list = Fields and whole?(operand, head, close)))
            and heads_near?(list, head, close, rest),
}

pub proc own_line(
    list: ListKind,
    followers: Followers,
    head: Int,               -- where the list's head starts
    close: Int,              -- where its closing bracket ends
    holders: Holders,
): (det own_line?) {
    ensure rule: own_line? iff
        (list is Parameters | FunctionParameters | Members
            or (only_closing?(followers) and heads_near?(list, head, close, holders)))

    expect signature: when list = Parameters, own_line?
    expect block: when list = Members, own_line?
    expect alone: when followers = Followers::Nil and holders = Holders::Nil, own_line?
    -- `f(a).len`: breaking `f`'s arguments would leave `.len` on the line of its `)`.
    expect method_after: when list = Arguments and followers = Then(Follower::Other, Followers::Nil),
        not own_line?
    -- `qqqqqqqqqq in {1, 2}`: a set literal does not break in place after a long left operand.
    expect set_right: when list = Elements and holders = Holder(14, Spans(head, close), Holders::Nil),
        not own_line?
}

-- `qqq = P { x := 1 }`: a record breaks in place after a long left operand. In `x = 1 and qqq =
-- P { x := 1 }`, it does not after a long operation that it is not the right operand of, and in
-- `qqq = -P { x := 1 }`, its operation's right operand ends with it but is more than the record.
expect records_break_in_place(
    n: Int,
    fs: Followers,
    head: Int,
    close: Int,
    start: Int,
    hs: Holders,
) {
    assume longer: start < head
    call right := own_line(Fields, fs, head, close, Holder(n, Spans(head, close), hs))
    call without := own_line(Fields, fs, head, close, hs)
    call elsewhere := own_line(Fields, fs, head, close, Holder(n, Absent, hs))
    call negated := own_line(Fields, fs, head, close, Holder(n, Spans(start, close), hs))
    expect exempt: right.own_line? = without.own_line?
    expect only_there: when n > 4, not elsewhere.own_line?
    expect only_the_whole_operand: when n > 4, not negated.own_line?
}
```

### Comments before an element

A comment keeps whether it starts its line, as it is
[content](#safety). Where a block comment starts the line of an element,
before its code, as in `/- lead -/ x`, a vertical list keeps the two
together, as rustfmt does: the line break that the list decides before
the element goes before the comments that start its line. Otherwise it
goes just before the element, and a comment after the opening bracket or
the comma on its line stays there, as in `f(/- c -/` ... So

```text
call w := g(
    /- lead -/ x, y,
)
```

is formatted as

```text
call w := g(
    /- lead -/ x,
    y,
)
```

`fmt::break_before` says how many of the comments before an element on its
line the line break goes before. The formatter's decision implements it,
proved in Lean:

```fren
pub proc break_before(
    comments: Nat,           -- the comments before the element on its line, after any token
    starts_line?,            -- the first of those comments starts its line
): (det before: Nat) {
    ensure rule: before = (if starts_line? then comments else 0)

    -- `/- lead -/ x` stays together.
    expect together: when starts_line?, before = comments
    -- `f(/- c -/` keeps the comment on the line of `(`.
    expect after_code: when not starts_line?, before = 0
}
```

### Right sides

The *right side* of a `:=` or `=>` is the expression after it: a
function's body, a constant's value, the definition of an `out`, of a
`let` member or of a `let` or `where` definition, the value of a field of
a record literal or update, the body of a `match` arm, or the value of a
table's row. (A `call`'s `:=` has none: what follows it is always a call,
whose arguments are a list.) An expression that does not fit on its line
continues only on lines indented past the column where it starts. So a
right side stays on its operator's line where it fits there, and
otherwise starts the next line, indented four spaces more than the
operator's line, with each line that continues it indented four more
again ([Indentation](#indentation)), unless it hangs, as a `match`, a
table, a call or a literal that is the whole right side does, as rustfmt
writes `let x = match y {`:

```text
pub fn lookup(ctx: Ctx, x: Name): Option<Ty> := match ctx {
    Ctx::Empty => None,
    Ctx::Bind(y, ty, rest) =>
        if y = x then Some(the_type_bound_there(ty, rest)) else lookup(rest, x),
}
```

A right side fits on a line when none of it must span several lines, as
for the elements of a list: it has no line comment, no comment that starts
a line, no line break that the formatter keeps, and no list that would be
vertical whatever line it were on, such as a `match` with arms or a call
whose arguments are too wide for one line; and when, with it on that line,
the line ends by column 100, counting what follows it up to where a line
may end, as rule 3 of [Lists and blocks](#lists-and-blocks) counts. So a
right side moves even where its operator's line is past column 100 already
at the operator, as the body of a `match` arm with a long pattern does, so
that the arms of one `match` are laid out alike. Inside the brackets
opened on the operator's line, as for a field of a record literal on one
line or a `let` in parentheses, a right side stays on that line, a long
line staying long and a `match` keeping its arms on the lines after, as a
list that is not its line's expression does.

A right side that does not fit on its operator's line moves to the next
line where it fits there, on one line. Where it does not fit there either,
it moves all the same, to be laid out again on its new line, unless it
*overflows*: a right side that is wholly a call, a parenthesized
expression, a literal, a record update, a Boolean block, a `match` or a
table stays on the operator's line, and only the elements or arms of its
bracket break, with its closing bracket indented as the operator's line,
where the operator's line fits up to that opening bracket. An `if` that
spans several lines does not hang: it starts the next line, so that its
`else` lines up with it, unless the author broke it by hand only before
its `then` or within its condition, which principle 6 keeps as written
(`either?` in `test/cli/fmt/right_sides.fren`, and `Evidence.md`'s
`backs`). A `match` with a `where` clause is not a whole `match`: it moves
(#687). Only a whole unit hangs: an operation that ends or starts with a
bracketed expression, as `not kind in {` or `"not " ++ enclosed(` does,
moves to the next line with the rest of the operation, and breaks there
only if it still does not fit. So a call that fits on the next line moves
there, one that does not hangs, and a literal after an operator moves:

```text
fn abs_of<V>(x: lang::Expr<V>): lang::Expr<V> :=
    lang::Expr::Method(lang::MethodName::Abs, x, lang::Expr::Nil)

let e: lang::Expr<lang::Id> := Binary(
    Mod,
    Binary(Add, summand_written(p.text), summand_written(q.text)),
    summand_written(k)
)

pub fn proof?(kind: Kind) :=
    not kind in {
        Kind::Cover,
        Kind::Vacuity,
        Kind::Reachability,
        Kind::Redundancy,
    }
```

An operation, an `if` or a chain broken by hand after a signature that
spans several lines, on the line that starts with the `)` of its
parameters, as `) :=` or `): Int :=`, always starts the next line, so that
it does not read as part of the signature. A whole `match`, table or
bracketed expression there hugs or moves as anywhere else, as rustfmt
writes `) -> T {`. A line that starts with another closing bracket, as
`} =>` after a condition with a vertical record literal, is not a
signature's, and its right side is laid out as any other.

A right side that the formatter keeps a line break in, outside its
brackets, is *broken by hand*, as after the comma of a guard or a
quantifier, before an `if`'s `then` or `else`, or around the operators of
a chain that keeps its line breaks ([Chains](#chains)): its line breaks
are content ([Safety](#safety)), so the author has already broken it where
it reads best, and the line break before it is content too. It starts the
next line where the source has it there, and otherwise stays on the
operator's line, as rustfmt hangs an expression, with the lines that
continue it indented four spaces more, unless its first line, up to its
first line break, would end past column 100 there, or it is an `if` with a
line break before an `else`, so that each `else` lines up with its `if`.
Where it starts the next line, each line that starts at one of those line
breaks is indented as its first line, rather than four more, so its links
line up as they were written, and lines that continue a link inside its
brackets are indented four more:

```text
pub fn innermost?(bindings: Set<Binding>, b: Binding, n: Id) := forall (c: Binding),
    when c in bindings and c.name = n, b.depth <= c.depth

out target :=
    if declared != [] then declared.at(0)
    else if opened.len = 1 then opened
    else prelude.at(0)

) :=
    exists (k l: ChoiceVariant), k != l and VariantForcing { variant := k } in alone
    and VariantForcing { variant := l } in rest
```

The expression of a clause, after the `:` of its name, as in `ensure r:`,
`expect e:` or a law's `law l(x: T):`, is a right side too where it is
wholly a chain, and its form is `Form::Chain`. It starts the next line
where the chain breaks on the clause's line, as `fmt::chain_layout` says,
so that the chain's operators are indented under its first operand rather
than under the clause, and it stays on the clause's line otherwise (#546's
decision 4). On the next line, the chain breaks again only if it still
does not fit there:

```text
expect substituted_under_binder:
    to_nameless(Names::Cons("z", Names::Nil), SUBSTITUTED) = Some(nsubst(0, Var(0), LAM_ONE))
        and nsubst(0, Var(0), LAM_ONE) = LAM_ONE
expect shifted:
    shift(1, 0, Lam(Anon::Anon, Boolean, App(Var(0), Var(1))))
        = Lam(Anon::Anon, Boolean, App(Var(0), Var(2)))
```

`fmt::right_side` decides whether a right side starts the next line, from
its form, the kind of its outermost expression, and from whether it fits
on the operator's line and on the next. A comment before it on its line
stays on the operator's line, and a line break that it decides goes
before the comments that start the right side's line, as for an element
of a list ([`fmt::break_before`](#comments-before-an-element)). The gap
gets a line break as `fmt::line_break` says for `Gap::RightSide`, which
breaks it where a comment forces it too. The parser gives the right sides,
their forms and the lists, and the formatter's decision implements
`fmt::right_side`, proved in Lean:

```fren
-- The outermost expression of a right side.
pub enum Form {
    Arms,                    -- a `match` or a table, with arms
    Conditional,             -- an `if`
    Bracketed,               -- a call, a parenthesized expression, a literal, a record update or a Boolean block
    Other,                   -- any other expression, such as an operation
    Chain,                   -- a chain that is a clause's expression (`fmt::chain_layout`)
}

-- A right side stays on the operator's line, its bracket's elements or arms breaking: it is wholly a
-- bracketed expression, a `match` or a table, and the line fits up to its opening bracket.
pub fn overflows?(form: Form, head_end: Int) :=
    head_end <= 100 and form is Form::Bracketed | Form::Arms

-- It fits on the operator's line, or stays there inside a bracket opened on that line.
pub fn fits_here?(broken?, inner?, line_end: Int) := inner? or (not broken? and line_end <= 100)

-- It fits on the next line, on one line.
pub fn fits_next?(broken?, next_end: Int) := not broken? and next_end <= 100

pub proc right_side(
    form: Form,
    chained?,                -- a line break that the formatter keeps is in it, outside its brackets
    written?,                -- the source has it on the next line
    ladder?,                 -- one of the line breaks in it is before an `else` of its `if`
    after_close?,            -- the operator's line starts with the `)` of a signature's parameters
    broken?,                 -- some of it must span several lines
    inner?,                  -- a bracket opened on the operator's line is open at the operator
    breaks?,                 -- for a clause's chain, it breaks on the operator's line (`fmt::chain_layout`)
    line_end: Int,           -- the column where the operator's line would end, with it on that line
    next_end: Int,           -- the column where its own line would end, with it on the next line
    first_end: Int,          -- the column where the operator's line would end, with it up to its first line break
    head_end: Int,           -- the same, with it up to its opening bracket
): (det next_line?) {
    ensure rule: next_line? iff
        (not inner?
            and ((after_close?
                    and (chained? or form is Form::Conditional | Form::Other | Form::Chain))
                or (if form = Form::Chain then breaks?
                    else if chained? then written? or ladder? or first_end > 100
                    else not fits_here?(broken?, inner?, line_end)
                    and (fits_next?(broken?, next_end) or not overflows?(form, head_end)))))

    -- `:= x + 1` stays on the operator's line where it fits.
    expect fits: when form != Form::Chain and not chained? and not after_close?
        and fits_here?(broken?, inner?, line_end), not next_line?
    -- `expect e:` `f(x) = g(y)`: a clause's chain starts the next line where it breaks on the clause's...
    expect clause_breaks: when form = Form::Chain and not inner? and breaks?, next_line?
    -- ...and stays on the clause's line where it does not, as `ensure r: x = match y {` ... `}`.
    expect clause_stays: when form = Form::Chain and not after_close? and not breaks?, not next_line?
    -- `:= match t {` ... `}` hugs its operator, as rustfmt's `let x = match y {` does.
    expect arms: when not chained? and not after_close? and form = Form::Arms and broken?
        and head_end <= 100, not next_line?
    -- `:= if c then a` ... `else b` spanning several lines starts the next line.
    expect conditional: when not chained? and not inner? and form = Form::Conditional and broken?,
        next_line?
    -- `:= f(` ... `)`: a call that fits on neither line hangs, and its arguments break.
    expect overflow: when not chained? and not after_close? and overflows?(form, head_end)
        and not fits_next?(broken?, next_end), not next_line?
    -- `:= not x in {` ... `}`: only a whole unit hangs, so an operation moves.
    expect whole_units: when not chained? and form = Form::Other
        and not fits_here?(broken?, inner?, line_end), next_line?
    -- A call that fits on the next line moves there, rather than breaking its arguments.
    expect moves_whole: when form != Form::Chain and not chained? and not fits_here?(broken?, inner?, line_end)
        and fits_next?(broken?, next_end), next_line?
    -- `) :=` takes no operation, `if` or chain on its line...
    expect after_signature: when after_close? and not inner? and (chained? or form is Form::Conditional | Form::Other),
        next_line?
    -- ...but a whole `match`, table or call hugs it as anywhere, as rustfmt writes `) -> T {`.
    expect hug_after_signature: when after_close? and not chained? and form = Form::Arms and broken?
        and head_end <= 100, not next_line?
    -- `:= forall (x: T),` ... `b`: a right side broken by hand stays where it was written, if its
    -- first line fits.
    expect hand_kept: when form != Form::Chain and chained? and not after_close? and not ladder?
        and first_end <= 100, next_line? iff (written? and not inner?)
    -- `:=` `if c then a` `else b`: the `else` of an `if` broken by hand lines up with its `if`.
    expect ladder_aligned: when form != Form::Chain and chained? and ladder? and not inner?, next_line?
}
```

### Chains

A *chain* is an operation of binary operators of one precedence, such as
`a and b and c`, `x + y - z`, `f(x) = g(y)` or `0 <= i < n`, with its
operands, none of which is an operation of that precedence. Where
`fren fmt` lays out a chain, it decides the line breaks before and after
its operators, as rustfmt does for a binary expression: the chain is on
one line where it fits, and otherwise *broken*, with a line break before
each of its operators and none after one, so each of its operands but the
first starts a line, after its operator. A chain with a membership's `in`
or a remainder's `mod`, which cannot start a line
([Lexical](Lang/Lexical.md#keywords)), is not laid out. The gaps get their
line breaks as `fmt::line_break` says for `Gap::Operator` and
`Gap::AfterOperator`, the one or the other breaking (`fmt::chain_side`),
and their blank lines go, as rustfmt drops those in
an expression.

The chains of an expression are laid out from the outside in, so the
loosest-binding operators break first, as rustfmt breaks the outermost
operation first, and an operand of a broken chain breaks in turn only if
its own line is too long. A line that starts with an operator of a broken
chain is indented four spaces more than the line that the chain starts
on, or, where a broken chain around it starts on that line too, four more
than that chain's operators, so the operators of an inner chain are
indented past those of the chain around it ([Indentation](#indentation)):

```text
ensure law:
    proved?
        and view(mv(l, src, dst), q)
            = (if under?(q, dst) then view(l, append(src, strip(q, dst)))
                else if under?(q, src) then Entry::Missing else view(l, q))
```

A chain breaks where it does not fit on its line:

1. it *must break*: a line break that formatting keeps, or a comment, is
   before its last operator, outside a list that cannot be on one line, or,
   where it has two operators or more, such a list is, as in
   `a and (match x {` ... `}) and c`; or the chain that is its whole last
   operand must break, so that the loosest operators break first, as in
   `ok? iff a > 0 and (match x {` ... `}) and b > 0`, whatever that operand
   would hug; or
2. its last operand does not *hug* it, and that operand holds a list that
   cannot be on one line, or the chain's line would end past column 100
   with the chain on one line, up to the first line break that formatting
   keeps in its last operand, counting what follows it up to where a line
   may end, as rule 3 of [Lists and blocks](#lists-and-blocks) counts.
   Where it has one operator, whose left operand holds a list that cannot
   be on one line, its line is the one where that list closes, from the
   closing bracket, as rustfmt keeps a right operand on the last line of a
   left one, as in `}).card >= 0`.

A last operand hugs a chain, breaking in place rather than the chain,
where its first line would end with the brace of a record literal or
update, a `match` or a table, and the line fits up to that brace, as
rustfmt keeps a right operand whose first line ends with `{` on its
operator's line; or where the chain has one operator, and its right
operand is wholly a call, a method call or a sequence or set literal, and
the line fits up to its bracket, after at most 4 columns, each token taking
its width and a space, as rustfmt keeps a right operand on the line of a
left one at most 4 wide, or where that operand would not fit on a line of
its own with its operator anyway, as it cannot be on one line, or is too
long (#546's decision 3). So breaking at `=` keeps a call on one line, or
is not done. A chain in a list on one line stays on that line, as a list in
it does:

```text
ensure r: total = a + b + c + match x {
    Boxed::Box(n) => n,
}
expect lam_bare: print_at(Level::Term, Lam(x, ty, body)) = append(
    Tokens::Cons(
        Token::Backslash,
        Tokens::Cons(Token::Ident(x), Tokens::Cons(Token::Colon, print_ty(ty)))
    ),
    Tokens::Cons(Token::Dot, print(body))
)
```

A chain that is not its line's expression keeps its line breaks as the
author wrote them, as principle 6 has it, since no rule decides them well
(`fmt::chain_kept`). It is one followed on its line, up to where a line
may end, by more than closing brackets and commas, as a guard's condition
before its body or an `if`'s condition before `then`; one after more than 4
columns on its line, each token taking its width and a space, as the body
of `when c, a = b` or the `else` branch of `if c then a else b + d`; and any
chain in one that keeps its line breaks. This is decided from the file's
structure, whatever its layout. What follows a chain counts up to where a
line may end: a comment, a line break that formatting keeps, or a gap whose
line break a list, a block, a right side or a chain that does not keep its
line breaks decides. What comes before it counts back to such a place, or
to an operator of a chain that does not keep its line breaks, outside
brackets that close before it, so that `ensure r:`, `:=` and `and (` leave
a chain its line's expression. So the guard's condition here keeps its
line breaks, and the chain after its comma, which starts its line, is laid
out:

```text
expect min: when eval(i, env, r) = Outcome::Defined(Value::Integer(m))
    and eval(i, env, args) = Outcome::Defined(Value::Cons(Value::Integer(n), Value::Nil)),
    eval(i, env, Expr::Method(MethodName::Min, r, args))
        = Outcome::Defined(Value::Integer(m.min(n)))
```

The parser gives the chains, their operators and the kind of their last
operand, and the formatter's decisions implement `fmt::chain_kept` and
`fmt::chain_layout`, proved in Lean:

```fren
-- Only closing brackets and commas follow it on its line.
pub fn closes_only?(followers: Followers) := match followers {
    Followers::Nil => true,
    Then(token, rest) => token is Follower::Closing | Follower::Comma and closes_only?(rest),
}

pub proc chain_kept(
    followers: Followers,    -- what follows it on its line, up to where a line may end
    before: Int,             -- the columns before it on its line, back to where a line may end
    holder_kept?,            -- the innermost chain that holds it keeps its line breaks
): (det kept?) {
    ensure rule: kept? iff (not closes_only?(followers) or before > 4 or holder_kept?)

    -- `if a and b then`: a condition before more of what holds it keeps its line breaks.
    expect condition: when followers = Then(Follower::Other, Followers::Nil), kept?
    -- `when c, a = b`: so does a chain after more than 4 columns on its line.
    expect after_guard: when before = 8, kept?
    -- `ensure r: a and b`: a clause's or a right side's chain is laid out...
    expect alone: when followers = Followers::Nil and before = 0 and not holder_kept?, not kept?
    -- ...and so is one after an opening bracket, as in `f((a and b))`.
    expect bracketed: when followers = Followers::Nil and before = 2 and not holder_kept?, not kept?
}

-- The last operand of a chain.
pub enum LastOperand {
    Brace,                   -- its first line ends with the brace of a record, a `match` or a table
    Bracket,                 -- it is wholly a call, a method call, or a sequence or set literal
    Other,                   -- any other expression
}

-- The last operand hugs the chain, breaking in place rather than the chain, where the line fits up to
-- its opening bracket: a brace ends its first line, or it is a bracketed list after a short left
-- operand, or one that would not fit on a line of its own anyway (#546's decision 3).
pub fn hugs?(
    operators: Int,
    last: LastOperand,
    list_last?,
    before: Int,
    head_end: Int,
    next_end: Int
) :=
    head_end <= 100
        and (last = LastOperand::Brace
            or (operators = 1
                and last = LastOperand::Bracket
                and (before <= 4 or list_last? or next_end > 100)))

-- A chain must break whatever its line: a line break kept, or a comment, is before its last operator,
-- outside a list, or, with two operators or more, a list that cannot be on one line is.
pub fn must_break?(operators: Int, forced_before?, list_before?) :=
    operators > 0 and (forced_before? or (list_before? and operators > 1))

pub proc chain_layout(
    operators: Int,          -- its operators
    flat?,                   -- it is in a list on one line
    forced_before?,          -- a line break kept, or a comment, is before its last operator, outside a list
    list_before?,            -- a list that cannot be on one line is before its last operator
    list_last?,              -- a list that cannot be on one line is in its last operand
    last: LastOperand,
    before: Int,             -- the columns before its last operand, each token taking its width and a space
    head_end: Int,           -- where its line would end, up to the brace or bracket of its last operand
    next_end: Int,           -- where its last operator and operand would end on a line of their own
    line_end: Int,           -- where its line would end, with it on that line, as rule 2 counts
    -- Of the chain that is its whole last operand, if any (0 operators if none): its operators,
    -- `forced_before?` and `list_before?`.
    last_operators: Int,
    last_forced?,
    last_list?,
): (det broken?) {
    ensure rule: broken? iff
        (operators > 0
            and not flat?
            and (must_break?(operators, forced_before?, list_before?)
                or must_break?(last_operators, last_forced?, last_list?)
                or (not hugs?(operators, last, list_last?, before, head_end, next_end)
                    and (list_last? or line_end > 100))))

    -- `ok? iff a > 0 and (match x {` ... `}) and b > 0`: where its last operand must break, so does
    -- it, the loosest first, whatever brace that operand holds.
    expect inner_breaks: when operators > 0 and not flat? and must_break?(last_operators, last_forced?, last_list?),
        broken?
    expect fits: when last_operators = 0 and not forced_before? and not list_before? and not list_last?
        and line_end <= 100, not broken?
    expect long: when operators > 0 and not flat? and last = LastOperand::Other and line_end > 100, broken?
    -- `x = match y {` ... `}`, `q = P {` ... `}`: a brace that ends the line hugs.
    expect braced: when last_operators = 0 and not forced_before? and not list_before?
        and last = LastOperand::Brace and head_end <= 100, not broken?
    -- `r = f(` ... `)`: a call hugs after a short left operand, and one that must split anyway...
    expect short_call: when last_operators = 0 and operators = 1 and not forced_before?
        and last = LastOperand::Bracket and before <= 4 and head_end <= 100, not broken?
    expect split_anyway: when last_operators = 0 and operators = 1 and not forced_before?
        and last = LastOperand::Bracket and list_last? and head_end <= 100, not broken?
    -- ...but `typeof(Ctx::Empty, e) = Some(` ... `)` breaks before `=` where `= Some(` ... `)` then fits
    -- on a line of its own (#546's decision 4).
    expect long_call: when operators = 1 and not flat? and last = LastOperand::Bracket and before > 4
        and not list_last? and next_end <= 100 < line_end, broken?
    -- `(table {` ... `}).card >= 0`: one operator stays after a left operand that spans lines...
    expect spanning_left: when last_operators = 0 and operators = 1 and not forced_before? and not list_last?
        and line_end <= 100, not broken?
    -- ...but `a and (match x {` ... `}) and c` breaks before each `and`.
    expect spanning_middle: when operators > 1 and not flat? and list_before?, broken?
    expect in_flat_list: when flat?, not broken?
}
```

Where a chain that breaks has one operator, `iff` or `=`, after a single
name no wider than 24 columns, a *short name*, it breaks after that
operator rather than before it, and its right operand starts the next line,
indented four spaces more, as a right side does. This amends principle 5
for that shape (#546): the name reads as what is being defined, and the
operator at the end of its line says how, as in `ensure rule: noted? iff`.
The right operand on its line is laid out as any chain is, and a clause
whose chain breaks so stays on the clause's line (`fmt::chain_side`):

```text
ensure rule: noted? iff
    (not interpreted?
        and consistent?
        and g in core
        and (exists (o: Output), clashes?(alone, alone_variants, rest, rest_variants, g, o))
        and match examples {
            Budget::All => true,
            Budget::AtMost(n) => earlier.card < n,
        })
```

```fren
-- A single name on the left of a chain's one `iff` or `=`, no wider than 24 columns.
pub fn short_name?(operators: Int, named?, width: Int) := operators = 1 and named? and width <= 24

pub proc chain_side(
    broken?,                 -- it breaks (`fmt::chain_layout`)
    operators: Int,          -- its operators
    named?,                  -- its left operand is a single name, and its one operator `iff` or `=`
    width: Int,              -- the width of that name
): (det after?) {
    ensure rule: after? iff (broken? and short_name?(operators, named?, width))

    -- `ensure rule: noted? iff` ... : a short name keeps its operator on its line...
    expect short: when broken? and operators = 1 and named? and width = 6, after?
    -- ...but a longer left operand, or several operators, break before each operator.
    expect not_named: when not named?, not after?
    expect several: when operators > 1, not after?
    expect whole: when not broken?, not after?
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
`Option<Set<Int>>` and `fn f<T>(x: T): T`, but `a < b` and `{ a, b }`, as
braces other than `::{` have spaces inside. Empty braces are written `{}`.
A comment always has a space on both sides, unless it starts or ends the
line or a comma follows it, and so does a unary `-` before another, `- -1`,
since `--` starts a comment. A comma takes no space before it even after a
block comment, as rustfmt writes `x /* c */, y`: `x /- c -/, y`.

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
    ensure comma_after_comment: when before = Comment and after = Comma, not space?
    ensure comment: when (before = Comment and after != Comma) or after = Comment, space?
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
    -- `x /- c -/, y`, as rustfmt writes `x /* c */, y`.
    expect commas_tight: when after = Comma, not space?
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

A `:=` or `=>` whose [right side](#right-sides) starts the next line
indents as a bracket does, until its right side ends: the right side's
first line is indented four spaces more than the operator's line, as an
element is, and a line that continues it four more again, past the column
where the right side starts, but for the links of an expression broken by
hand, which line up with its first line ([Right sides](#right-sides)). A
broken [chain](#chains) indents as a bracket does too, from its first
token to its last, so the lines that start with its operators are indented
four spaces more than the line it starts on. So a
`match` that is moved, as the operation that ends with it is, has its arms
indented eight spaces more than the operator's line, and its `}` four:

```text
pub fn f(t: T): Int :=
    base(t) + match t {
        T::A => 0,
        T::B =>
            if near?(t) then distance(t) + offset(t) else distance(t) * scale(t) + offset(t) + 1,
    }
```

A line that starts with a `|` of a `match` arm's pattern, or of a table
arm's, starts its alternative, so the alternatives of an or-pattern
written one per line line up. In a
[pattern test](Lang/Expressions.md#pattern-tests), such a line continues
its member, as any other line within an expression does:

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

A block's `{` that starts its line, after a line comment, is not a
continuation either: it is indented as its item, as rustfmt indents a
function's `{` on a line of its own.

A line that starts with the closing bracket of one that indents is
indented as the line that opens it. A comment on a line of its own is
indented as the line after it, but inside the brackets when that line
closes them. Other brackets, such as those of a grouping or an index, do
not indent. `fmt::indent` gives the indentation, in spaces, from the
brackets open at the start of the line, the innermost first, each with
whether it opens a list or block and the indentation of the line that
opens it. A line is indented from the line that opens the innermost of
those that indent, however many open on that line: in `f(g(` ... `))`,
the arguments of `g` are indented four spaces more than the line, not
eight. So the arms of a `match` in a clause are indented four spaces
more than the clause:

```fren
pub enum Bracket {
    Paren,                   -- `(`
    Square,                  -- `[`
    Curly,                   -- `{`
    PathCurly,               -- `::{`
    -- A `:=`, `=>` or clause's `:` whose right side starts the next line, until that ends, or a
    -- broken chain, from its first token to its last.
    Operator,
}

use self::Bracket::{Curly, Operator, Paren, PathCurly, Square}

-- The brackets open at the start of a line, the innermost first, each with whether it opens a list
-- or block and the indentation of the line that opens it.
pub enum OpenBrackets { Nil, Within(Bracket, Bool, Int, OpenBrackets) }

use self::OpenBrackets::Within

-- A bracket indents the lines inside it if it is a brace, an operator or opens a list or block.
pub fn indents?(bracket: Bracket, list?) := bracket is Curly | PathCurly | Operator or list?

-- Four more than the line that opens the innermost bracket that indents, or 0 outside every one.
pub fn base(brackets: OpenBrackets): Int := match brackets {
    OpenBrackets::Nil => 0,
    Within(bracket, list?, line, rest) => if indents?(bracket, list?) then line + 4 else base(rest),
}

-- The innermost open bracket indents.
pub fn innermost_indents?(brackets: OpenBrackets) := match brackets {
    OpenBrackets::Nil => false,
    Within(bracket, list?, _, _) => indents?(bracket, list?),
}

-- The indentation of the line that opens the innermost open bracket.
pub fn opener(brackets: OpenBrackets): Int := match brackets {
    OpenBrackets::Nil => 0,
    Within(_, _, line, _) => line,
}

pub enum LineStart { Closing, Starting, Continuing }

use self::LineStart::{Closing, Continuing, Starting}

pub proc indent(
    brackets: OpenBrackets,  -- the brackets open at the line's start
    start: LineStart,        -- what the line's first token does, or for a comment, the next line's
    comment?,                -- the line is a comment
): (det columns: Int) {
    -- A closing line's first token closes the innermost open bracket, which indents.
    assume closes_innermost: when start = Closing, innermost_indents?(brackets)

    ensure closing: when start = Closing,
        columns = (if comment? then base(brackets) else opener(brackets))
    ensure starting: when start = Starting, columns = base(brackets)
    ensure continuing: when start = Continuing, columns = base(brackets) + 4

    expect comment_inside: when comment?, columns >= base(brackets)
    expect outside: when brackets = OpenBrackets::Nil and start = Starting, columns = 0
    expect closing_below_its_elements: when start = Closing and not comment?, columns = base(brackets) - 4
    -- The arms of a `match` in a procedure's clause are indented by eight.
    expect match_in_a_clause: when brackets = Within(Curly, true, 4, Within(Curly, false, 0, OpenBrackets::Nil))
        and start = Starting, columns = 8
    -- Two brackets opened on one line indent once.
    expect two_on_a_line: when brackets = Within(Paren, true, 0, Within(Paren, true, 0, OpenBrackets::Nil))
        and start = Starting, columns = 4
}

-- A grouping or an index does not indent: a line inside one is indented as outside it.
expect others_do_not_indent(
    bracket: Bracket,
    line: Int,
    rest: OpenBrackets,
    start: LineStart,
    comment?,
) {
    assume not_a_brace: bracket is Paren | Square
    assume not_closing: start != Closing
    call inside := indent(Within(bracket, false, line, rest), start, comment?)
    call outside := indent(rest, start, comment?)
    expect same: inside.columns = outside.columns
}
```

## Comments at the end of lines

A comment at the end of a line is separated from the code by at least two
spaces. It stays in the column where it starts, if that leaves two spaces,
so comments aligned by hand stay aligned, and a change to one line does
not move the comments of the lines around it. On a line whose code is not
the code of the comment's line in the source, as where the formatter moves
a [right side](#right-sides) to the next line or joins one onto its
operator's line, the code before the comment is not what it was aligned
with, so the comment goes two spaces after the code. `fmt::comment_column`
gives the column of the comment's `--`, counted from 0:

```fren
pub proc comment_column(
    width: Nat,              -- the width of the line's code, with its indentation, after formatting
    original: Nat,           -- the column of the comment before formatting
    split?,                  -- the line's code is not the code of the comment's line in the source
): (det column: Int) {
    ensure kept: when not split? and original >= width + 2, column = original
    ensure moved: when split? or original < width + 2, column = width + 2

    expect gap: column >= width + 2
}
```

## Blank lines

At most one blank line separates two lines. There are none at the start of
a file or of a ```` ```fren ```` block, after a line that ends with a
bracket that [indents](#indentation), with a record update's `with` or
with a `:=` or `=>` whose right side starts the next line, or before a
line that starts with its closing bracket. A blank line is kept only where
formatting ends a line: one in a gap that a list or block joins onto one
line goes with the gap's line break, as one before a block's `{` does
(`fmt::line_break`), and one between two elements or members of a list or
block keeps the gap a line break. A file other than a Markdown spec ends
with a single newline.

A blank line goes before and after each top-level item that spans several
lines (#546), as Black puts blank lines around a function, where rustfmt
adds none and keeps those the author wrote. A run of one-line items keeps
the blank lines it has, packed or not. An item spans the lines that its
tokens are written on as laid out, from those of the `set_option ... in`
before it, which is part of it as an attribute is of a Rust function, so
an item after one on a line of its own spans several lines. Each line of a
token or comment that spans several counts, as of a block comment, and so
does each line of the comments that trail the item's last token, unless a
token follows them on their last line: a block comment that trails `}` and
ends on the next line goes with the item, and the blank line goes after it.
Whether an item spans several lines depends on its content, then, not on
how the source lays it out. The comments just above an item, with no blank
line between them and it in the source, go with it, as a doc comment goes
with a Rust function: the blank line goes above them, never between them
and the item. A comment that starts with `--~`, a ui test's annotation of
the line as many lines above it as it has `^` ([Testing](dev/Testing.md)),
goes with that line instead, and the comments above it are left as they
are. No blank line comes between an annotation and its line: an item is
not set apart where an annotation on or below its first line, before the
next item, reaches above where the blank line would go, as `--~^^` under a
one-line item reaches the line before it. Other comments, `--@` lines
included, are alike to the formatter. `fmt::apart` decides whether a line
between two items, or the first line of the later one, is set apart from
the item before by a blank line, from the lines of the two items, the
lines between them and the annotations after the later one:

```fren
-- The lines between two top-level items, from the later one up: for each, whether it
-- is a `--~` annotation, and the blank lines after it in the source.
pub enum Between { Nil, Line(Bool, Int, Between) }

-- How many of the lines between two items go with the later one: the comments just
-- above it, with no blank line after them, up to an annotation.
pub fn leading(between: Between): Int := match between {
    Between::Nil => 0,
    Between::Line(annotation?, blank, rest) =>
        if annotation? or blank > 0 then 0 else 1 + leading(rest),
}

-- The `--~` annotations on or below an item's first line, before the next item: for
-- each, how many lines it is below that line, blank lines counted, and how many lines
-- up it reaches, its count of `^`.
pub enum Annotations { Nil, At(Int, Int, Annotations) }

-- Some annotation reaches above the line `above` lines above the item's first line.
pub fn reaches_above?(annotations: Annotations, above: Int) := match annotations {
    Annotations::Nil => false,
    Annotations::At(distance, reach, rest) =>
        reach > distance + above or reaches_above?(rest, above),
}

pub proc apart(
    above: Nat,              -- how many lines the line is above its item's first line
    between: Between,        -- the lines between the item before and the item
    annotations: Annotations,  -- the annotations on or below the item's first line
    previous_first: Nat,     -- the line of the first token of the item before
    previous_last: Nat,      -- the last line of its last token, or of the comments trailing it
    first: Nat,              -- the line of the item's first token
    last: Nat,               -- the last line of its last token, or of the comments trailing it
): (det apart?) {
    -- Above an item and the comments that go with it, if it or the item before spans
    -- several lines, and no annotation reaches past there.
    ensure rule: apart? iff
        above = leading(between)
            and (previous_last > previous_first or last > first)
            and not reaches_above?(annotations, above)

    expect packed: when previous_last = previous_first and last = first, not apart?
    expect documented: when above < leading(between), not apart?
    expect left_above: when above > leading(between), not apart?
    expect annotated: when reaches_above?(annotations, above), not apart?
}
```

`fmt::item_lines` gives the lines of an item that `fmt::apart` reads,
from the lines of its first and last tokens and of the comments after it:
its last line is that of the comments that trail its last token, one
after another, unless a token follows them on their last line. Both the
formatter and the `formatting` job's check of blank lines compute an
item's lines with `FrenCli.Fmt.itemLines`, which is proved to meet
`fmt::item_lines`. The lines between two items are those after the
earlier item's last line and before the later item's first:

```fren
-- The comments after an item's last token, before the next token: for each, the lines it starts
-- and ends on.
pub enum Trailing { Nil, Comment(Int, Int, Trailing) }

-- Where the token after an item starts: none, at the end of the file, or on a line.
pub enum After { End, Line(Int) }

-- The line where the comments that go on from line `line` end, each starting on the line where the
-- one before it ends.
pub fn run_end(line: Int, trailing: Trailing): Int := match trailing {
    Trailing::Nil => line,
    Trailing::Comment(start, stop, rest) => if start = line then run_end(stop, rest) else line,
}

-- The next token starts by line `line`.
pub fn starts_by?(next: After, line: Int) := match next {
    After::End => false,
    After::Line(n) => n <= line,
}

pub proc item_lines(
    first_token: Nat,        -- the line its first token starts on
    last_token: Nat,         -- the line its last token ends on
    trailing: Trailing,      -- the comments after its last token, before the next token
    next: After,             -- where the next token starts
): (det first: Int, det last: Int) {
    let run: Int := run_end(last_token, trailing)
    ensure first_rule: first = first_token
    ensure last_rule: last = (if starts_by?(next, run) then last_token else run)

    expect untrailed: when trailing = Trailing::Nil, last = last_token
}

-- The layouts of #714, of an item from line 1 to a last token on line 4, which testing
-- evaluates, as the solver cannot unfold `run_end`. `} /- x` / `y -/`, then the next item: the
-- comment's last line is the item's.
set_option fren.evidence "random" in
expect item_lines_trailed() {
    call lines := item_lines(1, 4, Trailing::Comment(4, 5, Trailing::Nil), After::Line(6))
    expect first: lines.first = 1
    expect last: lines.last = 5
}

-- `} /- x` / `y -/ fn next`: a token follows the comment on its last line.
set_option fren.evidence "random" in
expect item_lines_followed() {
    call lines := item_lines(1, 4, Trailing::Comment(4, 5, Trailing::Nil), After::Line(5))
    expect last: lines.last = 4
}

-- `}` / `-- c`: a comment on a line of its own does not trail the item, nor one on the line after
-- a comment that does, as in `} -- c` / `/- d -/`.
set_option fren.evidence "random" in
expect item_lines_own_line() {
    call alone := item_lines(1, 4, Trailing::Comment(5, 5, Trailing::Nil), After::Line(6))
    call after := item_lines(
        1,
        4,
        Trailing::Comment(4, 4, Trailing::Comment(5, 5, Trailing::Nil)),
        After::End,
    )
    expect alone_last: alone.last = 4
    expect after_last: after.last = alone.last
}
```

For example, the formatter writes

```text
-- A `set_option ... in` and the item after it span two lines.
set_option fren.lint.constant_output "allow" in
proc zero(): (r: Int) { out r := 0 }

pub proc unit(): (r: Int) { out r := 1 }
proc two(): (r: Int) { out r := 2 }

pub proc unit_or_two(x?): (r: Int) {
    ensure one: when x?, r = 1
    ensure two: unless x?, r = 2
}
```

with the blank lines that it adds, and keeps no other. `fmt::blank_lines`
gives the number of blank lines kept before a line, with whether
`fmt::apart` sets it apart. The formatter's decisions implement both,
proved in Lean:

```fren
pub proc blank_lines(
    blank: Nat,              -- blank lines before the line in the input
    first?,                  -- the line is the first of its file or block
    after_open?,             -- the line before it ends with a bracket that indents, `with`, or `:=` or `=>`
    before_close?,           -- the line starts with the closing bracket of one
    apart?,                  -- `fmt::apart` sets the line apart from the item before it
): (det kept: Int) {
    ensure kept_rule: kept =
        if first? or after_open? or before_close? then 0 else if apart? or blank > 0 then 1 else 0

    expect at_most_one: kept <= 1
    expect never_added: when not apart?, kept <= blank
    expect set_apart: when apart? and not (first? or after_open? or before_close?), kept = 1
}

-- The blank lines before a block's `{` go: the `{` joins the line before it, so no line starts
-- there for `fmt::blank_lines` to keep them before. Between two members, they keep the line break.
expect blank_lines_with_breaks(blank: Nat, vertical?) {
    call brace := line_break(Gap::BlockBrace, vertical?, blank, false, false, false)
    call between := line_break(Gap::AfterComma, vertical?, blank, false, false, false)
    expect brace_joined: not brace.break?
    expect members_apart: when blank > 0, between.break?
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

So an element is added to a vertical list by adding a line. The members
of a block have no commas, as `fmt::ends_with_comma?` of `Members` says.
`fmt::trailing_comma` decides whether the last element of a list is
followed by a comma:

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
whose closing bracket starts a line. `fmt::trailing_comma_lint` states it.
It gives the lint `vertical?` for whether a line ends before the closing
bracket, as a vertical list's closing bracket starts a line, so
`never_reported` holds by construction: what it checks is that the
formatter writes the comma only in a vertical list. That the closing
bracket of a vertical list starts a line, and of no other, is the layout
of [Lists and blocks](#lists-and-blocks), which only the formatting tests
check:

```fren
set_option fren.evidence "enumerated" in
pub proc trailing_comma_lint(vertical?, allowed?) {
    use lint::unnecessary_trailing_comma

    call written := trailing_comma(false, vertical?, allowed?)
    -- Formatted, a line ends before the closing bracket exactly where the list is vertical.
    call reported := unnecessary_trailing_comma(vertical?)

    expect never_reported: when written.comma?, not reported.fires?
}
```

## Commas and comments

No line starts with a comma, as rustfmt writes them: a comma goes on the
line of the element before it, and a line break before it moves after it,
so that which side of a comma a line break is on is not content. Where
the element's line ends with a comment, `-- ...`, the comma goes before
the comment. So

```text
call h := heater(
    t  -- the temperature
    , true
)
```

is formatted as

```text
call h := heater(
    t,  -- the temperature
    true,
)
```

A comma does not move past a block comment, `/- ... -/`, that follows
code on its line, as in `x /- the width -/, y`. A block comment that
starts its line is placed as a line comment is, so that a comma after it
goes on the line of the element before, rather than after the comment,
as in `/- own line -/ ,`. `fmt::comment_piece` says which a comment is.
Commas are Fren's only separators: the members of a block have none, and
the `|` of an alternative and an operator may start a line.
`fmt::separators` places the commas, from the file's pieces in order: its
tokens, its comments and its line breaks. A comma that follows a line
break or a line comment goes before it, and then before any that precede
those:

```fren
pub enum Piece {
    Token,                   -- a token other than a comma
    Separator,               -- a comma
    LineComment,             -- `-- ...`, which ends its line, or a block comment that starts its line
    BlockComment,            -- `/- ... -/` after code on its line
    LineBreak,
}

use self::Piece::{BlockComment, LineBreak, LineComment, Separator, Token}

pub enum Pieces { Nil, Next(Piece, Pieces) }

use self::Pieces::Next

-- A comma cannot follow a line break or a line comment.
pub fn after_line?(piece: Piece) := piece is LineBreak | LineComment

-- The piece of a comment, `-- ...` or not, that starts its line or follows code on it.
pub proc comment_piece(line_comment?, starts_line?): (det piece: Piece) {
    out piece := if line_comment? or starts_line? then LineComment else BlockComment

    expect after_code: when not line_comment?, piece = BlockComment iff not starts_line?
}

-- `piece` before pieces whose commas are placed, and the commas at their start before it, if it
-- is a line break or a line comment.
pub fn put(piece: Piece, placed: Pieces): Pieces := match placed {
    Next(Separator, rest) =>
        if after_line?(piece) then Next(Separator, put(piece, rest)) else Next(piece, placed),
    _ => Next(piece, placed),
}

pub fn place(pieces: Pieces): Pieces := match pieces {
    Pieces::Nil => Pieces::Nil,
    Next(piece, rest) => put(piece, place(rest)),
}

-- Some comma follows a line break or a line comment.
pub fn misplaced?(pieces: Pieces) := match pieces {
    Pieces::Nil => false,
    Next(piece, rest) => after_line?(piece) and rest is Next(Separator, _) or misplaced?(rest),
}

-- The pieces but the commas.
pub fn others(pieces: Pieces): Pieces := match pieces {
    Pieces::Nil => Pieces::Nil,
    Next(Separator, rest) => others(rest),
    Next(piece, rest) => Next(piece, others(rest)),
}

pub fn commas(pieces: Pieces): Int := match pieces {
    Pieces::Nil => 0,
    Next(Separator, rest) => 1 + commas(rest),
    Next(_, rest) => commas(rest),
}

set_option fren.evidence "random" in
pub proc separators(input: Pieces): (det output: Pieces) {
    out output := place(input)

    expect none_misplaced: not misplaced?(output)
    expect others_kept: others(output) = others(input)
    expect commas_kept: commas(output) = commas(input)
    expect placed_already: when not misplaced?(input), output = input
}

-- `x  -- c`, a line break and `, y` is `x,  -- c`, a line break and `y`, whatever follows `y`.
-- Testing evaluates the recursive definitions, which the solver cannot unfold.
set_option fren.evidence "random" in
expect separators_before_the_comment(rest: Pieces) {
    let comma_y: Pieces := Next(Separator, Next(Token, rest))
    call written := separators(Next(Token, Next(LineComment, Next(LineBreak, comma_y))))
    call rest_written := separators(rest)
    let y: Pieces := Next(Token, rest_written.output)
    let comment_y: Pieces := Next(LineComment, Next(LineBreak, y))
    expect moved: written.output = Next(Token, Next(Separator, comment_y))
}

-- `x /- c -/, y` stays as it is.
set_option fren.evidence "random" in
expect separators_after_a_block_comment(rest: Pieces) {
    let comma_y: Pieces := Next(Separator, Next(Token, rest))
    call written := separators(Next(Token, Next(BlockComment, comma_y)))
    call rest_written := separators(rest)
    let y: Pieces := Next(Token, rest_written.output)
    expect kept: written.output = Next(Token, Next(BlockComment, Next(Separator, y)))
}
```

So a comma may move across line breaks, line comments and block comments
that start their lines, and nothing else moves. The order of a file's
tokens and comments that is part of its [content](#safety) is `fmt::order`
of its pieces, but its trailing commas and its `use` items: their order
with their commas placed, but for the line breaks. `fmt::ordering` states
that placing the commas first changes nothing, that it keeps the commas,
and that the other pieces keep their order. That a comma moves only across
those is the definition of `fmt::put`, and `fmt::order_starts` checks one
consequence: a token, a block comment or a comma at the start of the
pieces stays at the start of their order. The job that checks formatting
computes the order with the implementation of `fmt::ordering`, and checks
that formatting keeps it, of every spec in the repository and of each
laid out again. As that order leaves out the trailing commas and the
`use` items, the job reads all the pieces of what formatting writes, those
included, to check that they are not `fmt::misplaced?`.

```fren
-- The pieces but the line breaks.
pub fn unbroken(pieces: Pieces): Pieces := match pieces {
    Pieces::Nil => Pieces::Nil,
    Next(LineBreak, rest) => unbroken(rest),
    Next(piece, rest) => Next(piece, unbroken(rest)),
}

-- The order of the pieces that formatting keeps.
pub fn order(pieces: Pieces): Pieces := unbroken(place(pieces))

set_option fren.evidence "random" in
pub proc ordering(input: Pieces): (det output: Pieces) {
    out output := order(input)

    expect no_line_breaks: unbroken(output) = output
    expect placed_alike: order(place(input)) = output
    expect others_kept: others(output) = unbroken(others(input))
    expect commas_kept: commas(output) = commas(input)
}

-- A token, a block comment or a comma at the start stays at the start.
set_option fren.evidence "random" in
expect order_starts(rest: Pieces) {
    expect token_stays: order(Next(Token, rest)) = Next(Token, order(rest))
    expect block_comment_stays: order(Next(BlockComment, rest)) = Next(BlockComment, order(rest))
    expect comma_stays: order(Next(Separator, rest)) = Next(Separator, order(rest))
}

-- `x  -- c`, a line break and `, y` orders as `x`, `,`, `-- c` and `y`, whatever follows `y`.
set_option fren.evidence "random" in
expect order_before_the_comment(rest: Pieces) {
    let comma_y: Pieces := Next(Separator, Next(Token, rest))
    let written: Pieces := Next(Token, Next(LineComment, Next(LineBreak, comma_y)))
    let comma_comment_y: Pieces := Next(Separator, Next(LineComment, Next(Token, order(rest))))
    expect moved: order(written) = Next(Token, comma_comment_y)
}
```

## Imports

A *block* of imports is a run of `use` items on consecutive lines. Each
`use` in a block starts its line, ends a line, and shares its lines with no
comment or other token, and is not the item of a `set_option ... in`.
These lines are those of the file laid out: a `use` member that shares
its lines with no comment, and with no token but other members and its
block's braces, starts and ends its lines once its
[block](#lists-and-blocks) has one member to a line, and so is sorted
with the imports around it. A `use` that is its block's only member and
is joined onto the block's line is not in a block of imports. Any other
line, including a blank line or a comment, ends the block. So the imports
of a file can be kept in separate blocks, such as one for each module
they come from, and a comment above a `use` stays with it.

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

`fmt::in_block` decides whether a `use` is part of a block, from the
lines of the tokens next to it and the lines that comments are on:

```fren
-- Where the token next to a `use` is: there is none, as the `use` starts or ends the file, or it
-- is on a line.
pub enum Neighbour { Edge, OnLine(Int) }

use self::Neighbour::{Edge, OnLine}

-- Whether the token next to a `use`, if there is one, is on a line before `line`.
pub fn above?(n: Neighbour, line: Int) := match n {
    Edge => true,
    OnLine(l) => l < line,
}

-- Whether the token next to a `use`, if there is one, is on a line after `line`.
pub fn below?(n: Neighbour, line: Int) := match n {
    Edge => true,
    OnLine(l) => l > line,
}

-- The lines that comments are on, each line of a comment that spans several.
pub enum Lines { Nil, Line(Int, Lines) }

use self::Lines::Line

-- Whether one of `lines` is between `first` and `last`.
pub fn any_within?(lines: Lines, first: Int, last: Int) := match lines {
    Lines::Nil => false,
    Line(l, rest) => first <= l <= last or any_within?(rest, first, last),
}

pub proc in_block(
    first_line: Int,         -- the line where the `use` starts
    last_line: Int,          -- the line where it ends
    before: Neighbour,       -- where the token before it ends
    after: Neighbour,        -- where the token after it starts
    comments: Lines,         -- the lines that comments are on
    nested?,                 -- it is the item of a `set_option ... in`
): (det alone?, det sorted?) {
    assume in_order: first_line <= last_line

    -- It starts and ends its lines, which have no other token and no comment.
    ensure alone_rule: alone? iff
        (above?(before, first_line)
            and below?(after, last_line)
            and not any_within?(comments, first_line, last_line))
    ensure block_rule: sorted? iff (alone? and not nested?)

    expect shared: when before = OnLine(first_line), not sorted?
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
