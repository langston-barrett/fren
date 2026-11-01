#!/usr/bin/env python3
"""Drops the leading `|` of every table's row (`F0166`).

    python3 -I scripts/migrations/drop_table_bars.py [ROOT...]

A table's row no longer starts with `|`: commas separate the rows, and the
formatter puts each on a line of its own. This rewrites every `.fren` file
under each ROOT (default `.`), and every `fren`, `text` or unlabelled code
block of its Markdown files, outside `.lake`, `.git`, `book` and
`.claude`, but the explanation of `F0166`. It removes each `|` that starts a row of a table by conditions,
`table { ... }`, and the spaces after it, and prints each file it changes
with the number of `|`s removed. The `|` that starts an or-pattern, of a
`match` arm or of a table's arm, stays.
"""

import os
import re
import sys

TOKEN = re.compile(r'--[^\n]*|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z0-9_]*[?!]?|\|\||=>|::|\.\.=?|\s+|.', re.S)
FENCE = re.compile(r"^\s*```(\w*)\s*$")
SKIP = {".lake", ".git", "book", ".claude"}
# The explanation of `F0166`, whose erroneous example keeps its `|`s.
KEEP = {os.path.join("src", "FrenCore", "Codes", "F0166.md")}


def tokens(src):
    """The tokens of `src`, with their offsets, without comments and
    whitespace."""
    return [(m.group(), m.start()) for m in TOKEN.finditer(src) if not (m.group().isspace() or m.group().startswith("--"))]


def row_bars(src):
    """The offsets of the `|`s of `src` that start a row of a table by
    conditions: right after its `{` or after a `,` between its braces."""
    ts = tokens(src)
    bars = []
    # The kind of each open bracket: whether it is a table's `{`.
    stack = []
    for i, (t, _) in enumerate(ts):
        nxt = ts[i + 1][0] if i + 1 < len(ts) else ""
        if t in "{([":
            stack.append(t == "{" and i > 0 and ts[i - 1][0] == "table")
        elif t in "})]":
            if stack:
                stack.pop()
        if stack and stack[-1] and t in ("{", ",") and nxt == "|":
            bars.append(ts[i + 1][1])
    return bars


def drop(src, bars):
    """`src` without the `|`s at `bars`, nor the spaces after them."""
    out, last = [], 0
    for b in bars:
        out.append(src[last:b])
        last = b + 1
        while last < len(src) and src[last] in " \t":
            last += 1
    out.append(src[last:])
    return "".join(out)


def regions(path, text):
    """The parts of `text` that hold Fren: the whole of a `.fren` file, and
    the code blocks of a Markdown file that may."""
    if path.endswith(".fren"):
        yield 0, len(text)
        return
    off, start, lang = 0, 0, None
    for line in text.splitlines(keepends=True):
        m = FENCE.match(line)
        if m and lang is None:
            lang, start = m.group(1), off + len(line)
        elif m and m.group(1) == "":
            if lang in ("fren", "text", ""):
                yield start, off
            lang = None
        off += len(line)


def migrate(path):
    with open(path) as h:
        text = h.read()
    bars = [a + b for a, z in regions(path, text) for b in row_bars(text[a:z])]
    if bars:
        with open(path, "w") as h:
            h.write(drop(text, bars))
        print(f"{path}: {len(bars)}")


def main(roots):
    for root in roots or ["."]:
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = sorted(d for d in dirnames if d not in SKIP)
            for f in sorted(filenames):
                p = os.path.join(dirpath, f)
                if os.path.normpath(p) not in KEEP and (f.endswith(".fren") or f.endswith(".md")):
                    migrate(p)


if __name__ == "__main__":
    main(sys.argv[1:])
