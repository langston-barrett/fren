"""Writes the reviewer's brief: brief.md, with the review's facts and the
pull request's title and description.

Usage: compose.py TEMP_DIR KIND HOSTED

Reads TEMP_DIR/pr.json, and for a light check TEMP_DIR/previous-review.md
and TEMP_DIR/author-comment.md (prepare.sh, kind.py), and the facts in
the environment: REPO, PR, BRANCH, HEAD, BASE, MERGE, RUN and PREVIOUS.
HOSTED is `true` if this checkout's `.olean` files need no build. Prints
the brief.
"""

import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

HOSTED = {
    "true": (
        "This run restored `main`'s `.lake`, and `lake build --no-build Fren` "
        "found it up to date with this checkout, so `lake env "
        "/tmp/fren_test/fren_test --job ui FILE` runs them."
    ),
    "false": (
        "This checkout's `.olean` files would need a build, so a probe of "
        "those jobs is a suggestion in a finding, not something to run."
    ),
}

FULL = """# The kind of review

This is a full review of the head."""

LIGHT = """# The kind of review

This is a light check, not a full review. The pull request's previous
head, `{previous}`, has a review, below, and the author's last comment,
below it, says that the new head `{head}` changes it only by {what}.
{how}

The rest of this brief applies to the changes that you check. If the new
head changes anything else, do a full review of it instead,
as this brief describes, and give it a full review's first line: any
change beyond {what} gets a full review.

The review of `{previous}`:

{review}

The author's comment:

{comment}"""

HOW = {
    "fixes": (
        "Read `git diff {previous} {head}`, or, if the head was also rebased "
        "(`git merge-base --is-ancestor {previous} {head}` fails), `git "
        "range-diff OLD_BASE..{previous} {base}..{head}`, where OLD_BASE is "
        "`git merge-base {previous} {base}`. Confirm that each change answers "
        "a finding of the previous review that the comment lists, that it "
        "answers it well, and that nothing else changed."
    ),
    "rebase": (
        "Read `git range-diff OLD_BASE..{previous} {base}..{head}`, where "
        "OLD_BASE is `git merge-base {previous} {base}`. Confirm that the "
        "patch is unchanged apart from the resolutions of conflicts that the "
        "comment lists, and judge those resolutions."
    ),
}

WHAT = {"fixes": "fixes of that review's findings", "rebase": "a rebase"}


def quote(text):
    return "\n".join("> " + line for line in text.strip().splitlines())


def main():
    temp, kind, hosted = sys.argv[1:]
    env = os.environ
    with open(f"{temp}/pr.json") as f:
        pr = json.load(f)
    head = env["HEAD"]
    verdicts = [f"Review of {head}: no blocking issues", f"Review of {head}: blocking issues"]
    if kind == "full":
        section = FULL
    else:
        with open(f"{temp}/previous-review.md") as f:
            review = f.read()
        with open(f"{temp}/author-comment.md") as f:
            comment = f.read()
        facts = {"previous": env["PREVIOUS"], "head": head, "base": env["BASE"]}
        section = LIGHT.format(
            what=WHAT[kind], how=HOW[kind].format(**facts),
            review=quote(review), comment=quote(comment), **facts)
        verdicts.insert(1, f"Review of {head}: no blocking issues ({kind} only)")
    with open(f"{HERE}/brief.md") as f:
        brief = f.read()
    facts = {
        "REPO": env["REPO"], "PR": env["PR"], "BRANCH": env["BRANCH"], "HEAD": head,
        "BASE": env["BASE"], "MERGE": env["MERGE"], "RUN": env["RUN"],
        "HOSTED": HOSTED[hosted], "KIND_SECTION": section,
        "VERDICTS": "\n".join(f"    {v}" for v in verdicts),
        "TITLE": pr["title"], "BODY": quote(pr["body"] or "(no description)"),
    }
    # One pass, so that a placeholder in the pull request's own text, or in
    # a comment, stays as it is.
    sys.stdout.write(re.sub(r"\{\{([A-Z_]+)\}\}", lambda m: facts[m.group(1)], brief))


if __name__ == "__main__":
    main()
