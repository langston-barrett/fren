"""Frames one probe's output for probes.md, so that nothing it prints can
pass for the workflow's own text.

Usage: frame.py FILE STATUS LIMIT < OUTPUT

Prints a heading that names the probe, `fren check FILE`, the output as an
indented code block, and its exit status. Every line of the output is
indented four spaces, after control characters (`\\r` among them) are
removed and tabs expanded, so in CommonMark the whole output is one code
block that no line of it can close, and no heading, fence or HTML of its
own can start. The file's name loses its backticks and control characters.
OUTPUT is at most LIMIT bytes, which probe.sh's `head -c` keeps while the
probe runs; more means it was cut. test_frame.py checks this with a
CommonMark parser.
"""

import re
import sys

CONTROL = re.compile(r"[\x00-\x08\x0b-\x1f\x7f-\x9f  ]")


def clean(text):
    return CONTROL.sub("", text.expandtabs(4))


def name(file):
    return clean(file).replace("`", "").replace("\n", " ")[:200]


def frame(file, status, output, limit):
    cut = len(output) > limit
    text = clean(output[:limit].decode("utf-8", "replace"))
    lines = [f"## The probe `fren check {name(file)}`", ""]
    lines += ["    " + line for line in text.split("\n")]
    lines.append("")
    if cut:
        lines += [f"The output was cut at {limit} bytes.", ""]
    lines += [f"Exit status: {int(status)}.", ""]
    return "\n".join(lines) + "\n"


def main():
    file, status, limit = sys.argv[1:]
    sys.stdout.write(frame(file, status, sys.stdin.buffer.read(), int(limit)))


if __name__ == "__main__":
    main()
