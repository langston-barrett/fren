"""Checks the reviewer's review.md and writes the comment to post.

Usage: check.py REVIEW HEAD KIND RUN_URL NAMES COMMENT DOC...

Run by the `post` job, from the workflow's own commit, on the `review`
artifact. The review must:

- start with a first line that the brief allows for KIND;
- mark each numbered finding (a line that starts with `N.`) with exactly
  one of `[blocking]` and `[non-blocking…]`;
- have a `[blocking]` finding if and only if its verdict is `blocking
  issues`;
- hold nothing that looks like a token.

The names of machines are replaced: those in the file NAMES (the review
job's host and runner, one per line), and those that the DOCs, AGENTS.md
and Testing.md, give in the forms "Linux (NAME)" and "machines such as
NAME". The comment ends with a note that the review is advisory. If the
review fails a check, the comment says why instead, with the run's URL,
and does not start with "Review of", so that it counts as no review; the
script then fails.
"""

import re
import sys

ITEM = re.compile(r"^\d+\.\s")
MARK = re.compile(r"\[(blocking|non-blocking)[^\]]*\]")
TOKEN = re.compile(r"sk-ant-[\w-]{8,}|\bgh[pousr]_[A-Za-z0-9]{20,}|\bgithub_pat_\w{20,}")
DOC_NAMES = [
    re.compile(r"\b(?:Linux|macOS) \(([a-z][\w-]*)\)"),
    re.compile(r"\bmachines? such as ([a-z][\w-]*)"),
]
ADVISORY = (
    "*This review is by the `pr-review` workflow. It is static: it ran no "
    "probes and no fuzzer, and it relies on `pre-merge`, which passed on "
    "this head. It is advisory: the pull request's own text reaches the "
    "reviewer, and could steer it.*"
)


def allowed(head, kind):
    lines = {f"Review of {head}: no blocking issues", f"Review of {head}: blocking issues"}
    if kind in ("fixes", "rebase"):
        lines.add(f"Review of {head}: no blocking issues ({kind} only)")
    return lines


def problem(text, head, kind):
    """What is wrong with the review, or None."""
    lines = text.splitlines()
    first = lines[0] if lines else ""
    if first not in allowed(head, kind):
        return f"its first line is not a verdict that this review allows: `{first}`"
    if TOKEN.search(text):
        return "it holds something that looks like a token"
    blocking = False
    for line in lines[1:]:
        if not ITEM.match(line):
            continue
        marks = MARK.findall(line)
        if len(marks) != 1:
            return f"a finding is not marked with exactly one of [blocking] and [non-blocking]: `{line[:80]}`"
        blocking |= marks[0] == "blocking"
    if blocking != first.endswith(": blocking issues"):
        return "its verdict does not agree with its [blocking] findings"
    return None


def machine_names(names_file, docs):
    names = set()
    with open(names_file) as f:
        names |= {line.strip() for line in f if line.strip()}
    for doc in docs:
        with open(doc) as f:
            text = f.read()
        for pattern in DOC_NAMES:
            names |= set(pattern.findall(text))
    return names


def scrub(text, names):
    for name in sorted(names, key=len, reverse=True):
        text = re.sub(r"\b" + re.escape(name) + r"\b", "a machine", text, flags=re.IGNORECASE)
    return text


def comment(text, head, kind, run_url, names):
    """The comment to post, and whether the review passed."""
    reason = problem(text, head, kind) if text else "it wrote no `review.md`"
    if reason is None:
        return scrub(text, names) + "\n\n" + ADVISORY + "\n", True
    note = f"The `pr-review` workflow did not review {head}: {reason}. Its run is {run_url}.\n"
    return scrub(note, names), False


def main():
    review, head, kind, run_url, names_file, out, *docs = sys.argv[1:]
    try:
        with open(review) as f:
            text = f.read().strip()
    except FileNotFoundError:
        text = ""
    body, ok = comment(text, head, kind, run_url, machine_names(names_file, docs))
    with open(out, "w") as f:
        f.write(body)
    print(body)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
