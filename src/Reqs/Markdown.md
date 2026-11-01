# Markdown specs

A Markdown spec is a Markdown document whose Fren code is in fenced code
blocks marked `fren`:

````markdown
# Climate control

The thermostat never heats and cools at once.

```fren
mod climate
...
```
````

Everything else, including code blocks with any other language or none, is
prose. The `fren` blocks are read in order as one spec, so an item may span
several blocks with prose between them. Line and column numbers in
diagnostics are those of the Markdown file.

## Code blocks

Fences are read as CommonMark reads them, but for the differences in the
note below. A file's lines are split at
each `\n`, and a `\r` before it ends the line too. A line is split into the
spaces that it starts with, then a run of backticks or of tildes, then the
blanks (spaces and tabs) after the run, then the rest of the line, its *info
string*. The line is a *fence* if it has at most three spaces and a run of
at least three, and, for backticks, no backtick in its info string, so that
inline code at the start of a line, as in ```` ```fren ```` here, is not a
fence. `markdown::runs?` states how a line splits, over its text, and
`markdown::split` what follows from the split.

> **Note:** The reader differs from CommonMark in three ways. Only spaces
> count as indentation, and a tab is not expanded. A fence inside a block
> quote or a list item's container, such as `> ```fren`, is not a fence.
> And the info string keeps its trailing blanks, which CommonMark strips,
> so `fren` followed by a blank is not `fren` and is an error (`F0168`).
> Keeping them makes such a tag an error rather than a block read as
> `fren` that the author may have meant as something else, and keeps the
> split a matter of the text after the run, with no trimming at its end.



```fren
pub mod markdown

-- A space or a tab.
pub fn blank?(c: String) := c = " " or c = "\t"

-- `indent` is the spaces that `line` starts with, `run` the length of the
-- run of backticks or tildes after them, and `lead` the blanks after that.
set_option fren.lint.undecidable "allow" in
pub fn runs?(line: String, indent: Int, run: Int, lead: Int) :=
    (forall (k: Int), when 0 <= k < indent, line.at(k) = " ")
    and line.at(indent) != " "
    and (forall (k: Int), when indent <= k < indent + run, line.at(k) = line.at(indent))
    and (if line.at(indent) is "`" | "~" then line.at(indent + run) != line.at(indent) else run = 0)
    and (forall (k: Int), when indent + run <= k < indent + run + lead, blank?(line.at(k)))
    and not blank?(line.at(indent + run + lead))

set_option fren.lint.undecidable "allow" in
pub proc split(line: String, indent: Nat, run: Nat, lead: Nat): (
    det marker: String,   -- the character of the run, "`" or "~", or ""
    det info: String,     -- the rest of the line: its info string
    det fence?,
) {
    assume runs: runs?(line, indent, run, lead)

    out marker := if line.at(indent) is "`" | "~" then line.at(indent) else ""
    out info := line.slice(indent + run + lead, line.len - indent - run - lead)
    out fence? := indent <= 3 <= run and (marker = "~" or not info.contains?("`"))

    expect plain: when line = "```fren", fence? and info = "fren"
    expect plain_run: when line = "```fren", indent = 0 and run = 3 and lead = 0
}
```

A block whose info string is exactly `fren` is part of the spec, whichever
character fences it, and every other block is prose. One whose first word
is `fren`, up to a space, tab, `,` or `{`, such as `fren  example`,
`fren,ignore` or `fren` followed by a blank, looks like `fren` but is prose,
and is an error (`F0168`), so that a misspelt tag cannot drop a block
unnoticed. `fren example` is the [reference's](dev/Style.md#examples)
examples, which its tests check on their own, and is prose to the spec.
Indented code blocks are prose. `markdown::block_kind` states the kinds,
and `markdown::step`'s `kept?`, below, which lines are the spec's: those
in the body of a `fren` block. Every other line is read as an empty line,
so that positions in the file are kept:

```fren
pub enum BlockKind { Spec, Example, LooksLikeFren, Prose }

-- The info string's first word, up to a space, tab, `,` or `{`, is `fren`.
pub fn looks_like_fren?(info: String) :=
    info.starts_with?("fren ") or info.starts_with?("fren\t") or info.starts_with?("fren,") or info.starts_with?("fren{")

pub proc block_kind(info: String): (det kind: BlockKind) {
    ensure rule: kind = (if info = "fren" then BlockKind::Spec
        else if info = "fren example" then BlockKind::Example
        else if looks_like_fren?(info) then BlockKind::LooksLikeFren
        else BlockKind::Prose)

    expect spec_exactly: when kind = BlockKind::Spec, info = "fren"
    expect near_misses: when info in {"fren  example", "fren,ignore", "fren {.x}"}, kind = BlockKind::LooksLikeFren
    expect other_languages: when info in {"", "text", "frenzy", "lean"}, kind = BlockKind::Prose
}
```

A block opens at a fence, and its body is the lines after it, up to the
next fence of the same character with no info string and a run at least as
long as the one that opened it, which closes the block, so a block of four
backticks can show a block of three. A block that is not closed extends to
the end of the file, and is an error (`F0167`). `markdown::step` states how
the reader reads each line, from the line's text and from whether the lines
before it left it in a block, and which fence opened that block:

```fren
-- The fence that opened a block.
pub struct Opening { marker: String, run: Nat, info: String }

set_option fren.lint.undecidable "allow" in
pub proc step(
    inside?,              -- the lines before it left the reader in a block
    opening: Opening,     -- the fence that opened that block
    line: String,
    indent: Nat,          -- the line's runs, as `split` takes them
    run: Nat,
    lead: Nat,
): (
    det inside_after?,    -- the reader is in a block after the line
    det opening_after: Opening,
    det body?,            -- the line is in the body of a block
    det opens?,           -- the line opens a block
    det kept?,            -- the line is the spec's: in the body of a `fren` block
) {
    assume runs: runs?(line, indent, run, lead)

    call parts := split(line, indent, run, lead)
    call block := block_kind(opening.info)

    let closes? := inside? and parts.fence? and parts.marker = opening.marker and parts.run >= opening.run
        and parts.info = ""

    ensure opens: opens? iff not inside? and parts.fence?
    ensure body: body? iff inside? and not closes?
    ensure inside_after: inside_after? iff (if inside? then not closes? else parts.fence?)
    ensure kept: kept? iff body? and block.kind = BlockKind::Spec
    out opening_after := if opens? then Opening {
        marker := parts.marker,
        run := parts.run,
        info := parts.info,
    }
        else opening

    expect closes_longer: when inside? and opening.marker = "`" and opening.run = 3 and line = "````"
        and indent = 0 and run = 4, not inside_after?
    expect not_shorter: when inside? and opening.marker = "`" and opening.run = 4 and line = "```"
        and indent = 0 and run = 3, body?
    expect not_other_marker: when inside? and opening.marker = "~" and line = "```" and indent = 0 and run = 3,
        body?
}

#fren_check
```

A fence problem is a static error of the spec: it stops the spec's checks,
and those of the files after it, as any [static
error](View.md#static-errors) does, in both front ends.

## In Lean

`#fren_md "file.md"` reads the Markdown spec `file.md`, with the path
relative to the current Lean file, as if its `fren` blocks were written in
place of the command. The spec continues the current Lean file: it starts in
the current module, and its items are visible to the rest of the file,
including later `#fren_md` commands. As with the `fren` command, a file
whose name ends in `.md` is a Markdown spec, and any other file, such as
`rle.fren`, is read whole, as if all of it were one `fren` block, so that
Lean code can implement a spec written for the `fren` command. What
follows about a Markdown file read by `#fren_md` holds for such a file
too.

A Markdown file is named by its path relative to the Lean file, with `.`
and `..` resolved and `/` between components on every system, so that
every spelling of the path gives one name, as in `chapters/climate.md`,
even when another Markdown file reads it. An absolute path that shares no
root with the Lean file's is kept whole.
Diagnostics about the Markdown file are reported at the `#fren_md` command
in the Lean file, even for a file that another reads. Their text starts
with at most one name, and at most one position, such as
`chapters/climate.md:12:3:`, as follows. A diagnostic about a Markdown
file itself, such as a summary, a lint or a parse error, is named with
that file and its position there. A diagnostic about an item is placed by
the file that declares it, wherever it is checked:

- An item of a Markdown file is named with that file and its position
  there, even when another file's `#fren_check` reports it, as when one
  chapter checks the items of every chapter before it. When a `#fren_check`
  in the Lean file itself reports it, it is placed at the `#fren_check`,
  and its text starts with the Markdown file's name and position.
- An item of the Lean file is placed at its own position, even when a
  Markdown file's `#fren_check` reports it, so its text starts with no
  name.
- An imported item is placed at the `#fren_check` that reports it, since
  its position is in another module's text, so it is named with the file
  that holds that check.
- A diagnostic about an item that has no position is named with the file
  that declares it, if that is a Markdown file, without a position, and
  placed at the check. An item of the Lean file, or an imported item, with
  no position carries no name, even when a Markdown file checks it.

This holds through Markdown files that read others: an item is named with
the file that declares it, whichever file checks it, before or after, and
however deeply either is read.

Lake does not know that a Lean file depends on the Markdown files it reads,
so it rebuilds a module that uses `#fren_md` after
the Markdown changes only if the library declares those files with `needs`,
for example:

```toml
[[input_dir]]
name = "specs_md"
path = "src/Specs"
text = true
filter.extension = ["md"]

[[lean_lib]]
name = "Specs"
needs = ["specs_md"]
```

## With the `fren` command

The [`fren` command](Cli.md) reads any file whose name ends in `.md` as a
Markdown spec, and reports positions in it directly.
