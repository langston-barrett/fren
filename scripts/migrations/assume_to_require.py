#!/usr/bin/env python3
"""Writes the precondition of a function or a procedure as `require` (#669).

    python3 -I scripts/migrations/assume_to_require.py [ROOT...]

The precondition clause inside a function or a procedure is now written
`require n: e`, not `assume n: e` (`F0169`); the meaning is unchanged. The
`assume` of a global expectation's block stays. This rewrites every
`.fren` file under each ROOT (default `.`), every `fren`, `fren example`,
`text` or unlabelled code block of its Markdown files, and the Fren within
the Lean files of the tests (`src/FrenTest`, `src/FrenTestFiles`,
`src/FrenTestMain.lean`), written as commands or within string literals,
outside `.lake`, `.git`, `book` and `.claude`. It skips the explanation
and tests of `F0169`, and the front-end fuzzer, whose generators write an
item's members before its header. It prints each file it changes with the
number of keywords rewritten.

An `assume` is a clause's keyword where a member can start: followed by the
clause's name and `:`, or by an unlabelled Boolean block (`and {`, `or {`,
`iff {`, `one {`, or a leading `when` or `unless`). It is the keyword of a
global expectation's clause, and stays, when the item it is in, the last
item header before it, is `expect n(...)`; it is rewritten when that header
is a `proc` or an `fn`. One with no header before it in its region, as in a
fragment of a Markdown block, is reported and left for a person to decide.
"""

import os
import re
import sys

# `\n` within a Lean string literal is whitespace: the Fren of a test is
# often written as one.
TOKEN = re.compile(
    r'--[^\n]*|"(?:\\.|[^"\\])*"|\\n|[A-Za-z_][A-Za-z0-9_]*[?!]?|::|\s+|.', re.S
)
LEAN_TOKEN = re.compile(r'--[^\n]*|\\n|\\"|[A-Za-z_][A-Za-z0-9_]*[?!]?|::|\s+|.', re.S)
FENCE = re.compile(r"^\s*(```+)(.*?)\s*$")
SKIP = {".lake", ".git", "book", ".claude"}
# The explanation of `F0169`, whose erroneous example keeps its `assume`,
# and the front-end fuzzer, whose generators write each item's header
# after its members, which the change that introduced `require` (#669)
# converted by hand.
KEEP = {os.path.join("src", "FrenCore", "Codes", "F0169.md"), os.path.join("src", "FrenTest", "FuzzFrontends.lean")}
# The tests of `F0169`, which write `assume` on purpose.
KEEP |= {os.path.join("test", "cli", "syntax", "f0169_assume.fren")} | {
    os.path.join("test", "ui", "syntax", f"{k}.fren")
    for k in ("assume_in_proc", "assume_in_fn", "assume_in_method", "evidence_assume_in_proc",
              "assume_when_in_proc", "fn_det_result_before_assume", "fn_claim_before_assume",
              "method_det_result_before_assume", "proc_out_before_assume", "fn_out_before_assume",
              "fn_out_twice_before_assume", "fn_refines_before_assume", "method_out_before_assume",
              "proc_bare_before_assume", "fn_bare_before_assume", "method_bare_before_assume",
              "assume_in_proc_next_item", "assume_in_proc_named_later",
              "assume_then_grammar_error", "assume_in_trait_proc", "assume_under_setting",
              "assume_in_nested_trait")}
# The comparator of the front ends, whose `#guard`s report `F0169` on purpose.
KEEP |= {os.path.join("src", "FrenTest", "Frontends.lean")}
LEAN_DIRS = (os.path.join("src", "FrenTest") + os.sep, os.path.join("src", "FrenTestFiles") + os.sep)
LEAN_FILES = {os.path.join("src", "FrenTestMain.lean")}
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*[?!]?$")
BLOCKS = {"and", "or", "iff", "one"}
# An item's header: `proc p(`, `fn f(` or `fn f<T>(`, or `expect g(`, a
# global expectation's with a block. A member `expect n: e` has a `:`
# after its name, and a call's `p(` follows `:=`.
HEADER = re.compile(r"\b(proc|fn|expect)\s+[A-Za-z_][A-Za-z0-9_]*[?!]?\s*(?:<[^<>()]*>)?\(")


def sig(tokens):
    """The tokens that are not whitespace or comments, with their offsets."""
    return [(t, o) for t, o in tokens if not (t.isspace() or t == "\\n" or t.startswith("--"))]


def keyword_sites(src, lean):
    """The offsets of the `assume`s of `src` that start a clause."""
    pat = LEAN_TOKEN if lean else TOKEN
    ts = sig([(m.group(), m.start()) for m in pat.finditer(src)])
    out = []
    for i, (t, o) in enumerate(ts):
        if t != "assume":
            continue
        prev = ts[i - 1][0] if i > 0 else ""
        if prev in (".", "::"):
            continue
        nxt = [x for x, _ in ts[i + 1 : i + 3]]
        labelled = len(nxt) == 2 and IDENT.match(nxt[0]) and nxt[1] == ":"
        bare = (len(nxt) == 2 and nxt[0] in BLOCKS and nxt[1] == "{") or (nxt[:1] in (["when"], ["unless"]))
        if labelled or bare:
            out.append(o)
    return out


def regions(path, text):
    """The parts of `text` that hold Fren: the whole of a `.fren` or Lean
    file, and the code blocks of a Markdown file that may."""
    if not path.endswith(".md"):
        yield 0, len(text)
        return
    off, start, fence, keep = 0, 0, None, False
    for line in text.splitlines(keepends=True):
        m = FENCE.match(line)
        if m and fence is None:
            fence, start = m.group(1), off + len(line)
            keep = m.group(2).strip() in ("fren", "fren example", "text", "")
        elif m and fence is not None and m.group(1) == fence and not m.group(2).strip():
            if keep:
                yield start, off
            fence = None
        off += len(line)


def migrate(path, undecided):
    with open(path) as h:
        text = h.read()
    lean = path.endswith(".lean")
    sites = []
    for a, z in regions(path, text):
        region = text[a:z]
        for o in keyword_sites(region, lean):
            headers = list(HEADER.finditer(region, 0, o))
            if not headers:
                line = text.count("\n", 0, a + o) + 1
                undecided.append(f"{path}:{line}")
                continue
            if headers[-1].group(1) != "expect":
                sites.append(a + o)
    if sites:
        out, last = [], 0
        for s in sites:
            out.append(text[last:s])
            out.append("require")
            last = s + len("assume")
        out.append(text[last:])
        with open(path, "w") as h:
            h.write("".join(out))
        print(f"{path}: {len(sites)}")


def wanted(p, f):
    n = os.path.normpath(p)
    if n in KEEP:
        return False
    if f.endswith(".fren") or f.endswith(".md"):
        return True
    return f.endswith(".lean") and (n in LEAN_FILES or n.startswith(LEAN_DIRS))


def main(roots):
    undecided = []
    for root in roots or ["."]:
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = sorted(d for d in dirnames if d not in SKIP)
            for f in sorted(filenames):
                p = os.path.join(dirpath, f)
                if wanted(p, f):
                    migrate(p, undecided)
    for u in undecided:
        print(f"{u}: an `assume` with no item before it in its block, left as it is", file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1:])
