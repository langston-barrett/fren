# Contributing to Fren

How Fren is built and tested, and where it is going.

New requirements are added to the reference first, and checked with Fren
before they are implemented. The pages of the reference that contain `fren`
blocks are read by thin Lean files in `src/Reqs` with `#fren_md`, so `lake
build` elaborates them: `src/Reqs/Lang.lean` reads every page in
`src/Reqs/Lang/` except Modules and Calls, which, like the other chapters,
have their own Lean file and module. `lake test` checks the same pages with
the `fren` command, and Lean checks them on `main`
([Testing](Testing.md#own-requirements)). Pages that are only prose, such
as this one, are not read.

- [Architecture](Architecture.md): design principles and libraries
- [Testing](Testing.md): the kinds of tests and where they live
- [Writing the reference](Style.md): the register and layout of its chapters
- [Roadmap](Roadmap.md): what comes next, and open questions

## Building the book

`mdbook build` writes the reference to `book/`. It needs
[mdBook](https://github.com/rust-lang/mdBook) and mdbook-spec, the Rust
Reference's preprocessor, which renders [rule
identifiers](Style.md#rule-identifiers) as anchors. mdbook-spec is not
published; it is in the `tools/mdbook-spec` directory of
[rust-lang/reference](https://github.com/rust-lang/reference). Install the
versions that CI uses (`.github/workflows/book.yml`):

```sh
cargo install --locked mdbook --version 0.5.4
cargo install --locked --git https://github.com/rust-lang/reference \
  --rev 3989fe91f1a601b51684a582ad17b2503f221787 mdbook-spec
```

The book's page "Rules and their requirements" is written when it is
built, by `scripts/rules_report.py`, from the test driver,
`.lake/build/bin/fren_test`: run `lake build fren_test` before `mdbook
build`, or the page is a placeholder that says so. A driver built from an
older checkout writes that checkout's report.

The `book` job builds the book on every pull request, in `pre-merge`, and
on `main`, in `lean ci`, and publishes nothing. It builds no Lean: it runs
the test driver that its run's `lake test` built, which shard 0 uploads.
