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

Fences are read as CommonMark reads backtick fences. A line is split into
the spaces that it starts with, the backticks after them, and the rest,
whose text without the spaces and tabs around it is the *info string*. The
line is a *fence* if it has at most three spaces, at least three
backticks, and no backtick in its info string, so that inline code at the
start of a line, as in ```` ```fren ```` here, is not a fence. A block
opens at a fence and closes at the next fence with no info string and at
least as many backticks as the one that opened it, so a block of four
backticks can show a block of three. A block that is not closed extends to
the end of the file, and is an error (`F0167`). `markdown::fence` and
`markdown::closes` state this:

```fren
pub mod markdown

pub proc fence(
    indent: Nat,     -- the spaces that the line starts with
    run: Nat,        -- the backticks after them
    info: String,    -- the rest of the line, without the spaces and tabs around it
): (det fence?) {
    ensure rule: fence? iff indent <= 3 <= run and not info.contains?("`")

    expect plain: when indent = 0 and run = 3 and info = "fren", fence?
    expect indented_code: when indent = 4, not fence?
    expect inline_code: when run = 4 and info = "```fren ````", not fence?
}

pub proc closes(
    opening: Nat,    -- the backticks of the fence that opened the block
    indent: Nat,
    run: Nat,
    info: String,
): (det closes?) {
    call line := fence(indent, run, info)

    ensure rule: closes? iff line.fence? and run >= opening and info = ""

    expect longer_run: when indent = 0 and run = 4 and opening = 3 and info = "", closes?
    expect shorter_run: when run = 3 and opening = 4, not closes?
    expect with_info: when info = "text", not closes?
}
```

A block whose info string is exactly `fren` is part of the spec, and every
other block is prose. One whose first word is `fren`, up to a space, tab,
`,` or `{`, such as `fren  example` or `fren,ignore`, looks like `fren` but
is prose, and is an error (`F0168`), so that a misspelt tag cannot drop a
block unnoticed. `fren example` is the
[reference's](dev/Style.md#examples) examples, which its tests check on
their own, and is prose to the spec. Blocks fenced with `~~~`, and indented
code blocks, are prose. `markdown::block_kind` states the kinds:

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

#fren_check
```

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
