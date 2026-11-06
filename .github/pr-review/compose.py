"""Writes the reviewer's brief: AGENTS.md's "Reviews by separate agents"
and "Keeping the front ends together", verbatim, then brief.md, which says
what differs on CI, with the review's facts and the pull request's title
and description.

Usage: compose.py TEMP_DIR KIND

Run by prepare.sh in the workflow's own checkout, whose AGENTS.md it
reads, never the pull request's. Reads TEMP_DIR/pr.json, and for a light
check TEMP_DIR/previous-review.md and TEMP_DIR/request.md (kind.py), and
the facts in the environment: REPO, PR, HEAD, BASE, RUN and PREVIOUS.
Prints the brief.
"""

import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
# `python3 -I` leaves the script's directory off the path.
sys.path.insert(0, HERE)

from check import PREFIX, verdicts  # noqa: E402
SECTIONS = ["Reviews by separate agents", "Keeping the front ends together"]

FULL = "This is a full review of the head."

LIGHT = """This is a light check, not a full review: the "{what}" check that the
process above describes. The pull request's previous head, `{previous}`,
has a review, quoted below, and the comment quoted below it says that
the new head `{head}` changes it only by {change}. `pre-approval` passed on
the new head: the workflow runs only then.

{how}

If the new head changes anything else, don't review it here: a light
check runs on a smaller model than a full review. Write a review whose
first line says blocking issues, with one `[blocking]` finding that names
what changed beyond the request and says the head needs a full review;
the author or coordinator then posts a comment that names the head
without asking for a light check, and reruns the workflow by hand
(`gh workflow run pr-review -f pr=N -f post=N`), which gives the same
head a full review.

In the light check, judge only what changed since `{previous}`: the
diff from it, or, for a rebase, what the range-diff shows changed in
the patch. Code that this leaves unchanged had its review: raise a point
about it only if it is `[blocking]`. Mark any other point about it
`[non-blocking]`, never `[non-blocking, fix before merge]`, and say that
it goes to the area's queue rather than into this pull request.

The review of `{previous}`:

{review}

The comment that asks for the check:

{request}"""

HOW = {
    "fixes": (
        "Read `.review/fixes.patch`, the diff from the previous head to the "
        "new one (absent if the new head was also rebased), and "
        "`.review/range-diff.txt`. Confirm that each change answers a "
        "non-blocking finding of the previous review that the comment "
        "lists, that it answers it well, and that nothing else changed."
    ),
    "rebase": (
        "Read `.review/range-diff.txt`, the range-diff of the previous "
        "head's patch against the new head's. Confirm that the patch is "
        "unchanged apart from the resolutions of conflicts that the comment "
        "lists, and judge those resolutions."
    ),
}

CHANGE = {"fixes": "fixes of that review's non-blocking findings", "rebase": "a rebase"}


def quote(text):
    return "\n".join("> " + line for line in text.strip().splitlines())


def sections(agents):
    """The top-level sections of AGENTS.md that the brief includes."""
    parts = re.split(r"^(?=# )", agents, flags=re.MULTILINE)
    found = {p.splitlines()[0][2:].strip(): p.strip() for p in parts if p.startswith("# ")}
    return "\n\n".join("#" + found[name] for name in SECTIONS)


def main():
    temp, kind = sys.argv[1:]
    env = os.environ
    with open(f"{temp}/pr.json") as f:
        pr = json.load(f)
    head = env["HEAD"]
    if kind == "full":
        section = FULL
    else:
        with open(f"{temp}/previous-review.md") as f:
            review = f.read()
        with open(f"{temp}/request.md") as f:
            request = f.read()
        section = LIGHT.format(
            what=f"{kind} only", change=CHANGE[kind], how=HOW[kind], previous=env["PREVIOUS"],
            head=head, review=quote(review), request=quote(request))
    with open("AGENTS.md") as f:
        agents = sections(f.read())
    with open(f"{HERE}/brief.md") as f:
        brief = f.read()
    facts = {
        "REPO": env["REPO"], "PR": env["PR"], "HEAD": head, "BASE": env["BASE"],
        "RUN": env["RUN"], "AGENTS": agents, "KIND": section,
        "VERDICTS": "\n".join(f"    {v}" for v in verdicts(head, kind)),
        "PREFIX": PREFIX,
        "TITLE": pr["title"], "BODY": quote(pr["body"] or "(no description)"),
    }
    # One pass, so that a placeholder in the pull request's own text, or in
    # a comment, stays as it is.
    sys.stdout.write(re.sub(r"\{\{([A-Z_]+)\}\}", lambda m: facts[m.group(1)], brief))


if __name__ == "__main__":
    main()
