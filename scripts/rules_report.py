#!/usr/bin/env python3
"""An mdBook preprocessor that adds the report of the reference's rules
(`Reqs/dev/Style#rules-and-requirements`) to the book, as the page
`dev/Rules.md`, under "Writing the reference" (`dev/Style.md`).

The report is `fren_test --rules-report`, run from the book's root. The
test driver is the one that `FREN_TEST` names, which must run: the `book`
workflow sets it to the driver that its caller's run built. Otherwise it
is `.lake/build/bin/fren_test`, which `lake build fren_test` builds; without
one, the page is a placeholder that says how to write it. The report is
never committed, so that pull requests that change its rows do not
conflict over it.

It also renders the links of each rule's identifier line, `r[ID] LINKS`
(`Reqs/dev/Style#rule-identifiers`), small, at the start of the rule, and
leaves `r[ID]` alone on its line, which is all that mdbook-spec reads.
`python3 scripts/rules_report.py test` tests this.
"""

import html
import json
import os
import re
import shutil
import subprocess
import sys

PATH = "dev/Rules.md"
PARENT = "dev/Style.md"


PLACEHOLDER = """# Rules and their requirements

This page is written from the test driver when the book is built. Run
`lake build fren_test`, then `mdbook build`, to write it here.
"""


def report(root):
    driver = os.environ.get("FREN_TEST")
    if driver and not os.path.exists(driver):
        sys.exit(f"rules_report: FREN_TEST names {driver}, which does not exist")
    if not driver:
        driver = os.path.join(root, ".lake", "build", "bin", "fren_test")
        if not os.path.exists(driver):
            print(f"rules_report: no test driver at {driver}, so the page of the rules is a placeholder", file=sys.stderr)
            return PLACEHOLDER
    # `lake env` finds the toolchain's shared libraries where the driver
    # needs them; CI's stripped driver needs only the system's.
    cmd = [driver, "--rules-report"]
    if shutil.which("lake"):
        cmd = ["lake", "env"] + cmd
    out = subprocess.run(cmd, cwd=root, capture_output=True, text=True)
    if out.returncode != 0:
        sys.exit(f"rules_report: `{' '.join(cmd)}` failed (exit {out.returncode}):\n{out.stdout}{out.stderr}")
    return out.stdout


def add(items, chapter):
    """Adds `chapter` to the sub-items of the chapter `PARENT` in `items`,
    returning whether it found it."""
    for item in items:
        ch = item.get("Chapter") if isinstance(item, dict) else None
        if ch is None:
            continue
        if ch.get("path") == PARENT:
            chapter["parent_names"] = ch["parent_names"] + [ch["name"]]
            number = ch.get("number")
            chapter["number"] = number + [len(ch["sub_items"]) + 1] if number else None
            ch["sub_items"].append({"Chapter": chapter})
            return True
        if add(ch["sub_items"], chapter):
            return True
    return False


RULE_LINE = re.compile(r"(r\[[^\]\s]+\]) (\S.*)")
FENCE = re.compile(r"\s*(```+|~~~+)")


def render_links(content):
    """`content`, a chapter's Markdown, with the links of each rule's
    identifier line outside code blocks on a line of their own, as small
    code."""
    out = []
    fence = None
    for line in content.split("\n"):
        f = FENCE.match(line)
        if f and fence is None:
            fence = f.group(1)
        elif f and fence is not None and f.group(1).startswith(fence) and not line.strip().strip(fence[0]):
            fence = None
        m = RULE_LINE.fullmatch(line) if fence is None else None
        if m:
            out.append(m.group(1))
            out.append(f'<small class="rule-links"><code>{html.escape(m.group(2))}</code></small><br>')
        else:
            out.append(line)
    return "\n".join(out)


def render_all(items):
    """Renders the links of every chapter of `items` (`render_links`)."""
    for item in items:
        ch = item.get("Chapter") if isinstance(item, dict) else None
        if ch is not None:
            ch["content"] = render_links(ch["content"])
            render_all(ch["sub_items"])


def test():
    assert render_links("r[a.b] lang::p::{c, d}\nText.") == \
        'r[a.b]\n<small class="rule-links"><code>lang::p::{c, d}</code></small><br>\nText.'
    assert render_links("r[a.b]\nText.") == "r[a.b]\nText."
    assert render_links("```text\nr[a.b] lang::p\n```\nr[a.c] q<r") == \
        '```text\nr[a.b] lang::p\n```\nr[a.c]\n<small class="rule-links"><code>q&lt;r</code></small><br>'
    assert render_links("````\n```\nr[a.b] p\n````\n") == "````\n```\nr[a.b] p\n````\n"
    print("rules_report: tests pass")


def main():
    if sys.argv[1:] == ["test"]:
        test()
        return
    if len(sys.argv) > 1:
        # `supports RENDERER`: every renderer.
        return
    context, book = json.load(sys.stdin)
    render_all(book["items"])
    chapter = {
        "name": "Rules and their requirements",
        "content": report(context["root"]),
        "number": None,
        "sub_items": [],
        "path": PATH,
        # mdbook-spec reads every chapter's `source_path`, as a key and the
        # base of its links, and panics on none.
        "source_path": PATH,
        "parent_names": [],
    }
    if not add(book["items"], chapter):
        sys.exit(f"rules_report: the book has no chapter `{PARENT}`")
    json.dump(book, sys.stdout)


if __name__ == "__main__":
    main()
