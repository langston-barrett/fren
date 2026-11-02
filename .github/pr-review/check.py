"""Checks the reviewer's review.md and writes the comment to post.

Usage: check.py REVIEW HEAD KIND RUN_URL COMMENT

The review's first line must be one that the brief allows for KIND
(compose.py). The runner's names are replaced, since a comment names no
machine. If the review is missing or its first line is not allowed, the
comment says so instead, with the run's URL, and does not start with
"Review of", so that it counts as no review; the script then fails.
"""

import os
import re
import socket
import sys


def allowed(head, kind):
    lines = {f"Review of {head}: no blocking issues", f"Review of {head}: blocking issues"}
    if kind in ("fixes", "rebase"):
        lines.add(f"Review of {head}: no blocking issues ({kind} only)")
    return lines


def scrub(text):
    names = {socket.gethostname(), os.environ.get("RUNNER_NAME", "")}
    for name in sorted((n for n in names if n), key=len, reverse=True):
        text = re.sub(re.escape(name), "the runner", text, flags=re.IGNORECASE)
    return text


def main():
    review, head, kind, run_url, comment = sys.argv[1:]
    problem = None
    try:
        with open(review) as f:
            text = f.read().strip()
    except FileNotFoundError:
        problem, text = "it wrote no `review.md`", ""
    if problem is None:
        first = text.splitlines()[0] if text else ""
        if first not in allowed(head, kind):
            problem = f"the first line of its `review.md` is not a verdict: `{first}`"
    if problem is None:
        body = scrub(text) + "\n"
    else:
        body = (f"The `pr-review` workflow did not review {head}: {problem}. "
                f"Its run is {run_url}.\n")
        if text:
            body += "\nWhat it wrote:\n\n" + "\n".join("> " + l for l in scrub(text).splitlines()) + "\n"
    with open(comment, "w") as f:
        f.write(body)
    print(body)
    sys.exit(0 if problem is None else 1)


if __name__ == "__main__":
    main()
