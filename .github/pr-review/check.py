"""Checks the reviewer's review.md and writes the comment to post.

Usage: check.py REVIEW HEAD KIND RUN_URL NAMES COMMENT
       check.py leaks REVIEW SECRET_VAR...

The first form is the `post` job's, run from the workflow's own commit on
the `review` artifact. The review must:

- start with a first line that the brief allows for KIND (`verdicts`);
- mark each numbered finding (a line that starts with `N.`) with exactly
  one of `[blocking]`, `[non-blocking]` and `[non-blocking, …]`;
- have a `[blocking]` finding if and only if its verdict is `blocking
  issues`;
- hold nothing that looks like a token, and no image, HTML or link that
  loads from a host other than github.com, since GitHub's image proxy
  fetches an image's URL when the comment is shown, which could carry data
  out;

Names of machines are replaced: those in the file NAMES (the review job's
host and runner, one per line), and any word whose SHA-256 is in
machines.sha256. The comment ends with a note that the review is
advisory. If the review fails a check, the comment says why instead, with
the run's URL, and does not start with the verdict's prefix, so that it
counts as no review; the script then fails.

The second form is the `review` job's, which holds the secrets, run before
the review leaves it: it fails if the review holds any of the values of
the environment variables SECRET_VAR, or of their distinctive parts, as
they are, reversed, in hexadecimal or in base64, whatever separates their
characters.
"""

import base64
import hashlib
import os
import re
import sys

# The first line of a review: `Review of <full head sha>: VERDICT`, as
# AGENTS.md has a review start, so that the comment counts as the review of
# the head. Whether it should is the user's to decide; to post it as
# something else, change only this prefix (and `kind.py`, which reads
# AGENTS.md's form, then no longer counts these comments as reviews).
PREFIX = "Review of"

HERE = os.path.dirname(os.path.abspath(__file__))
ITEM = re.compile(r"^\d+\.\s")
MARK = re.compile(r"\[(blocking|non-blocking(?:,[^\]]*)?)\]")
LOOSE_MARK = re.compile(r"\[(?:non-)?blocking[^\]]*\]")
TOKEN = re.compile(r"sk-ant-[\w-]{8,}|\bgh[pousr]_[A-Za-z0-9]{20,}|\bgithub_pat_\w{20,}")
URL = re.compile(r"\b(?:https?|ftp)://([^/\s)\]>\"'`]+)", re.IGNORECASE)
IMAGE = re.compile(r"!\[[^\]]*\]\s*[(\[]|<\s*(?:img|picture|source|video|audio|iframe|object|embed)\b",
                   re.IGNORECASE)
ADVISORY = (
    "*This review is by the `pr-review` workflow. It is advisory: the pull "
    "request's own text reaches the reviewer, and could steer it. It ran "
    "the probes in its job's `probes.md`, with the binaries that `pre-merge` "
    "built, and suggests any others in its findings.*"
)


def verdicts(head, kind):
    """The first lines that a review of `head` of this kind may have."""
    lines = [f"{PREFIX} {head}: no blocking issues"]
    if kind in ("fixes", "rebase"):
        lines.append(f"{PREFIX} {head}: no blocking issues ({kind} only)")
    lines.append(f"{PREFIX} {head}: blocking issues")
    return lines


def github_host(host):
    host = host.lower().split("@")[-1].split(":")[0]
    return host == "github.com" or host.endswith(".github.com")


def problem(text, head, kind):
    """What is wrong with the review, or None."""
    lines = text.splitlines()
    first = lines[0] if lines else ""
    if first not in verdicts(head, kind):
        return f"its first line is not a verdict that this review allows: `{first}`"
    if TOKEN.search(text):
        return "it holds something that looks like a token"
    if IMAGE.search(text):
        return "it holds an image or embedded HTML, which loads from elsewhere when shown"
    for host in URL.findall(text):
        if not github_host(host):
            return f"it links to a host other than github.com: `{host}`"
    blocking = False
    for line in lines[1:]:
        if not ITEM.match(line):
            continue
        marks = MARK.findall(line)
        if len(marks) != 1 or len(LOOSE_MARK.findall(line)) != 1:
            return f"a finding is not marked with exactly one of [blocking] and [non-blocking]: `{line[:80]}`"
        blocking |= marks[0] == "blocking"
    if blocking != first.endswith(": blocking issues"):
        return "its verdict does not agree with its [blocking] findings"
    return None


def hashed_names(path=os.path.join(HERE, "machines.sha256")):
    with open(path) as f:
        return {line.strip() for line in f if line.strip() and not line.startswith("#")}


def scrub(text, names, hashes=frozenset()):
    """`text` with each name in `names`, and each word whose SHA-256 is in
    `hashes`, replaced, ignoring case."""
    for name in sorted(names, key=len, reverse=True):
        text = re.sub(r"\b" + re.escape(name) + r"\b", "a machine", text, flags=re.IGNORECASE)

    def word(m):
        h = hashlib.sha256(m.group(0).lower().encode()).hexdigest()
        return "a machine" if h in hashes else m.group(0)

    return re.sub(r"[A-Za-z0-9][A-Za-z0-9_-]*", word, text)


def comment(text, head, kind, run_url, names, hashes=frozenset()):
    """The comment to post, and whether the review passed."""
    reason = problem(text, head, kind) if text else "it wrote no `review.md`"
    if reason is None:
        return scrub(text, names, hashes) + "\n\n" + ADVISORY + "\n", True
    note = f"The `pr-review` workflow did not review {head}: {reason}. Its run is {run_url}.\n"
    return scrub(note, names, hashes), False


def alnum(text):
    return re.sub(r"[^A-Za-z0-9]", "", text)


def forms(secret):
    """What a copy of `secret`, or of one of its distinctive parts, could
    look like, with only its letters and digits: the part itself, reversed,
    in hexadecimal, and in base64 from each of the three alignments."""
    parts = {secret} | {p for p in re.split(r"[-_.]", secret) if len(p) >= 12}
    for p in list(parts):
        parts |= {p[i:i + 16] for i in range(0, max(len(p) - 15, 1), 8)}
    found = set()
    for p in parts:
        raw = p.encode()
        found |= {alnum(p), alnum(p[::-1]), raw.hex(), raw.hex().upper()}
        for i in range(3):
            chunk = raw[i:]
            chunk = chunk[: len(chunk) - len(chunk) % 3]
            if chunk:
                found.add(alnum(base64.b64encode(chunk).decode()))
                found.add(alnum(base64.urlsafe_b64encode(chunk).decode()))
    return {f for f in found if len(f) >= 12}


def leaks(text, secrets):
    """Whether `text` holds a copy of one of the `secrets` (`forms`)."""
    squeezed = alnum(text)
    lower = squeezed.lower()
    for secret in secrets:
        if secret and any(f in squeezed or f.lower() in lower for f in forms(secret)):
            return True
    return False


def main():
    if sys.argv[1] == "leaks":
        review, *names = sys.argv[2:]
        with open(review) as f:
            text = f.read()
        sys.exit(1 if leaks(text, [os.environ.get(n, "") for n in names]) else 0)
    review, head, kind, run_url, names_file, out = sys.argv[1:]
    try:
        with open(review) as f:
            text = f.read().strip()
    except FileNotFoundError:
        text = ""
    with open(names_file) as f:
        names = {line.strip() for line in f if line.strip()}
    body, ok = comment(text, head, kind, run_url, names, hashed_names())
    with open(out, "w") as f:
        f.write(body)
    print(body)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
