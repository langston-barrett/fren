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

A fence is a line that starts with three backticks, after at most three
spaces. A `fren` block opens at a fence whose info string is exactly
`fren`, and closes at the next fence with no info string. Blocks fenced with
`~~~`, and indented code blocks, are prose.

## In Lean

`#fren_md "file.md"` reads the Markdown spec `file.md`, with the path
relative to the current Lean file, as if its `fren` blocks were written in
place of the command. The spec continues the current Lean file: it starts in
the current module, and its items are visible to the rest of the file,
including later `#fren_md` commands.

Diagnostics about the Markdown file are reported at the `#fren_md` command,
with text that starts with the Markdown file's name and position, such as
`climate.md:12:3:`. A diagnostic about an item is placed by the file that
declares it, wherever it is checked:

- An item of a Markdown file is named with that file and its position
  there, even when another file's `#fren_check` reports it, as when one
  chapter checks the items of every chapter before it. When a `#fren_check`
  in the Lean file itself reports it, it is placed at the `#fren_check`,
  and its text starts with the Markdown file's name and position.
- An item of the Lean file is placed at its own position, even when a
  Markdown file's `#fren_check` reports it.
- An imported item is placed at the `#fren_check` that reports it, since
  its position is in another module's text.

This holds through Markdown files that read others: an item is named with
the file that declares it, whichever file checks it, before or after.

A Markdown file read by another Markdown file is named by its path
relative to the Lean file, as in `chapters/inner.md:12:3:`, and a
diagnostic starts with one name and position, that of the file that
declares the item, however deeply it is read.

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
