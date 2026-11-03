"""Decides which review a pull request's head gets, from its comments.

Usage: kind.py PR_JSON EVENT OUT_DIR
       kind.py verdict PR_JSON SHA
       kind.py wording PREVIOUS HEAD

PR_JSON is `gh pr view --json headRefOid,comments`. EVENT is the
workflow's event. The first form prints `key=value` lines for
`$GITHUB_OUTPUT`: `kind` (`full`, `fixes`, `rebase` or `skip`), `reason`,
and, for a light check or a wording-only skip, `previous`, the previously
reviewed head. For either it writes the previous review to
OUT_DIR/previous-review.md and the comment that asks for it to
OUT_DIR/request.md. The second form prints the verdict of the last review
of SHA, or nothing, for prepare.sh's skip of an update from `main`, so
that both read a review the same way. The third form, run by prepare.sh
in a repository that has both commits, prints why HEAD cannot skip as
wording only after PREVIOUS (`wording_problem`), or nothing if it can.

AGENTS.md allows two light checks, each only when the previous head's
review was clean: "rebase only", when the new head only rebases it, and
"fixes only", when it only fixes that review's non-blocking findings. It
also lets a head that only fixes the wording of such a review skip any
check: "wording only" (below). The author, the reviewers and the
coordinator all post under one login, so a comment's login says nothing
about who wrote it. So each of the three needs a comment that is not a
review, names the head (by at least its first 7 hex digits), and starts
with "fixes only", "rebase only" or "wording only"; the latest such
comment that names the head decides. The head that it checks against is
the one reviewed last before that comment, which must be another head
than this one, and whose review must have found no blocking issues.
Otherwise the head gets a full review. A workflow_run skips a head that
already has a review.

A "wording only" request gives `skip` on any event, with `previous` set
and a reason that starts with `WORDING`, so that prepare.sh can check
what it can of the rule mechanically: the head's only parent is
`previous`, and the head changes neither AGENTS.md nor anything under
`.github/` (`wording_problem`). If it passes, prepare.sh prints
"Nothing to review: wording only: ...", a line that no other skip
prints; otherwise the head gets a full review. The rest is the
coordinator's to confirm before the merge: that each change answers a
"fix before merge" finding of the previous review that the request
lists and changes only prose as AGENTS.md defines it, which leaves out
text that decides behaviour or process, and that nothing else changed.
A later comment that names the head without starting with one of the
three gets it a full review, as for a light check.

Anyone who can read the repository can comment, so only the comments of
those who can push count, as reviews and as requests: those whose
`authorAssociation` is OWNER, MEMBER or COLLABORATOR, as in claude.yml.
Any other comment is ignored, so an outsider's forged verdict or request
changes nothing.

Whether the head is only an update from `main` of a reviewed head is
decided by prepare.sh, which has the commits.
"""

import json
import re
import subprocess
import sys

REVIEW = re.compile(r"Review of ([0-9a-f]{40}): (no blocking issues|blocking issues)")
LIGHT = {"fixes only": "fixes", "rebase only": "rebase", "wording only": "wording"}
PUSHERS = {"OWNER", "MEMBER", "COLLABORATOR"}
SHA = re.compile(r"\b[0-9a-f]{7,40}\b")
# How the reason of a wording-only skip starts, and so the line that
# prepare.sh prints for it, which no other skip prints.
WORDING = "wording only:"


def first_line(body):
    return body.strip().splitlines()[0] if body.strip() else ""


def reviews(comments):
    """The reviews among the comments, in order: (sha, clean, comment)."""
    found = []
    for c in comments:
        m = REVIEW.match(first_line(c["body"]))
        if m:
            found.append((m.group(1), m.group(2) == "no blocking issues", c))
    return found


def light_kind(body):
    """`fixes`, `rebase` or `wording` if the comment starts so, ignoring
    case and leading markup such as `**` or a quote."""
    text = body.lstrip(" \t\r\n*_`\"'>#").lower()
    for prefix, kind in LIGHT.items():
        if text.startswith(prefix):
            return kind
    return None


def names(body, sha):
    """Whether the comment names the commit `sha` by a prefix of 7 or more
    hex digits."""
    return any(sha.startswith(m) for m in SHA.findall(body.lower()))


def counted(pr):
    """The comments that count, oldest first: those of the repository's
    owner, members and collaborators."""
    return sorted((c for c in pr["comments"] if c.get("authorAssociation") in PUSHERS),
                  key=lambda c: c["createdAt"])


def decide(pr, event):
    head = pr["headRefOid"]
    comments = counted(pr)
    found = reviews(comments)
    if event == "workflow_run" and any(sha == head for sha, _, _ in found):
        return {"kind": "skip", "reason": f"{head} already has a review"}
    review_ids = {id(c) for _, _, c in found}
    about = [c for c in comments if id(c) not in review_ids and names(c["body"], head)]
    if not about:
        return {"kind": "full", "reason": "no comment names the head"}
    request = about[-1]
    kind = light_kind(request["body"])
    if kind is None:
        return {"kind": "full", "reason": "the last comment that names the head asks for no light check"}
    before = [r for r in found if r[2]["createdAt"] <= request["createdAt"]]
    if not before:
        return {"kind": "full", "reason": "no head has a review before the request"}
    previous, clean, review = before[-1]
    if previous == head:
        return {"kind": "full", "reason": "the request comes after a review of the head itself"}
    if not clean:
        return {"kind": "full", "reason": f"the review of {previous} found blocking issues, so the head gets a fresh review"}
    if kind == "wording":
        # prepare.sh adds what `wording_problem` found and prints it as
        # "Nothing to review: wording only: ...", the line that AGENTS.md
        # has the coordinator look for.
        kind, reason = "skip", (
            f"{WORDING} {previous} has a clean review, and the last comment that names the head says "
            "that the head only fixes that review's wording")
    else:
        reason = f"the last comment that names the head starts with \"{kind} only\""
    return {
        "kind": kind,
        "reason": reason,
        "previous": previous,
        "previous_review": review["body"],
        "request": request["body"],
    }


def verdict(pr, sha):
    """The verdict of the last review of `sha` among the comments, or None."""
    found = [first_line(c["body"]) for s, _, c in reviews(counted(pr)) if s == sha]
    return found[-1][len(f"Review of {sha}: "):] if found else None


def git(*args):
    return subprocess.run(["git", *args], check=True, capture_output=True, text=True).stdout


def wording_problem(previous, head):
    """Why `head` cannot skip as wording only after `previous`, or None:
    its only parent must be `previous`, and it must change neither
    AGENTS.md nor anything under `.github/`. Runs git in the current
    directory."""
    if git("rev-list", "--parents", "-n", "1", head).split() != [head, previous]:
        return f"{head} is not one commit on top of {previous}: its only parent must be {previous}"
    changed = git("diff", "--no-ext-diff", "--no-textconv", "--no-renames", "--name-only", "-z",
                  previous, head).split("\0")
    # The process and the workflow, whose prose decides how reviews go.
    held = [p for p in changed if p == "AGENTS.md" or p.startswith(".github/")]
    if held:
        return f"{head} changes {held[0]}, which a wording-only head never changes"
    return None


def main():
    if sys.argv[1] == "wording":
        previous, head = sys.argv[2:]
        print(wording_problem(previous, head) or "")
        return
    if sys.argv[1] == "verdict":
        pr_json, sha = sys.argv[2:]
        with open(pr_json) as f:
            print(verdict(json.load(f), sha) or "")
        return
    pr_json, event, out_dir = sys.argv[1:]
    with open(pr_json) as f:
        decision = decide(json.load(f), event)
    if "previous" in decision:
        with open(f"{out_dir}/previous-review.md", "w") as f:
            f.write(decision.pop("previous_review"))
        with open(f"{out_dir}/request.md", "w") as f:
            f.write(decision.pop("request"))
    for key, value in decision.items():
        print(f"{key}={value}")


if __name__ == "__main__":
    main()
