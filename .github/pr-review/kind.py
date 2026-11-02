"""Decides which review a pull request's head gets, from its comments.

Usage: kind.py PR_JSON EVENT OUT_DIR

PR_JSON is `gh pr view --json headRefOid,comments,commits`. EVENT is the
workflow's event. It prints `key=value` lines for `$GITHUB_OUTPUT`:
`kind` (`full`, `fixes`, `rebase` or `skip`), `reason`, and, for a light
check, `previous`, the previously reviewed head. For a light check it
writes the previous review to OUT_DIR/previous-review.md and the author's
comment to OUT_DIR/author-comment.md.

A light check, as AGENTS.md describes, needs the author's last comment
that is not a review to start with "fixes only" or "rebase only", to be
posted after the head was committed, and the head reviewed last before
that comment to be another one; for "rebase only", that head's review must
have found no blocking issues. Otherwise the head gets a full review. The
fixes of blocking findings get a light check too, as the reviewers'
practice is. A workflow_run skips a head that
already has a review. Whether the head is only an update from `main` of a
reviewed head is decided by the workflow, which has the commits.
"""

import json
import re
import sys

REVIEW = re.compile(r"Review of ([0-9a-f]{40}): (no blocking issues|blocking issues)")
LIGHT = {"fixes only": "fixes", "rebase only": "rebase"}


def first_line(body):
    return body.strip().splitlines()[0] if body.strip() else ""


def reviews(comments):
    """The reviews among the comments, oldest first: (sha, clean, comment)."""
    found = []
    for c in comments:
        m = REVIEW.match(first_line(c["body"]))
        if m:
            found.append((m.group(1), m.group(2) == "no blocking issues", c))
    return found


def light_kind(body):
    """`fixes` or `rebase` if the comment starts so, ignoring case and
    leading markup such as `**` or a quote."""
    text = body.lstrip(" \t\r\n*_`\"'>#").lower()
    for prefix, kind in LIGHT.items():
        if text.startswith(prefix):
            return kind
    return None


def decide(pr, event):
    head = pr["headRefOid"]
    author = pr["author"]["login"]
    comments = sorted(pr["comments"], key=lambda c: c["createdAt"])
    found = reviews(comments)
    if event == "workflow_run" and any(sha == head for sha, _, _ in found):
        return {"kind": "skip", "reason": f"{head} already has a review"}
    review_ids = {id(c) for _, _, c in found}
    own = [c for c in comments if c["author"]["login"] == author and id(c) not in review_ids]
    if not own:
        return {"kind": "full", "reason": "the author has posted no comment"}
    last = own[-1]
    kind = light_kind(last["body"])
    if kind is None:
        return {"kind": "full", "reason": "the author's last comment asks for no light check"}
    committed = [c["committedDate"] for c in pr["commits"] if c["oid"] == head]
    if committed and last["createdAt"] < committed[0]:
        return {"kind": "full", "reason": "the author's light-check comment predates the head"}
    before = [r for r in found if r[2]["createdAt"] <= last["createdAt"] and r[0] != head]
    if not before:
        return {"kind": "full", "reason": "no earlier head has a review"}
    previous, clean, review = before[-1]
    if kind == "rebase" and not clean:
        return {"kind": "full", "reason": f"the review of {previous}, which the head rebases, found blocking issues"}
    return {
        "kind": kind,
        "reason": f"the author's last comment starts with \"{kind} only\"",
        "previous": previous,
        "previous_review": review["body"],
        "author_comment": last["body"],
    }


def main():
    pr_json, event, out_dir = sys.argv[1:]
    with open(pr_json) as f:
        decision = decide(json.load(f), event)
    if "previous" in decision:
        with open(f"{out_dir}/previous-review.md", "w") as f:
            f.write(decision.pop("previous_review"))
        with open(f"{out_dir}/author-comment.md", "w") as f:
            f.write(decision.pop("author_comment"))
    for key, value in decision.items():
        print(f"{key}={value}")


if __name__ == "__main__":
    main()
