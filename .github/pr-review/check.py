"""Checks the reviewer's review.md and writes the comment to post.

Usage: check.py REVIEW HEAD KIND RUN_URL NAMES COMMENT
       check.py leaks REVIEW SECRET_VAR...

The first form is the `post` job's, run from the workflow's own commit on
the `review` artifact. The review must:

- start with a first line that the brief allows for KIND (`verdicts`);
- mark each numbered finding (a line that starts with `N.` or `N)`, after
  at most two spaces) with exactly one of `[blocking]`, `[non-blocking]`
  and `[non-blocking, …]`, and, under a clean verdict, have no
  `[blocking]` mark anywhere;
- have a `[blocking]` finding if and only if its verdict is `blocking
  issues`;
- say which probes it ran and which it could not, in a paragraph that
  starts with `Probes:` (`PROBES`);
- hold nothing that looks like a token, no Markdown image (even in code),
  and no link to a host other than github.com, since GitHub's image proxy
  fetches an image's URL when the comment is shown, which could carry
  data out.

Names of machines are replaced: those in the file NAMES (the review job's
host and runner, one per line), and any word whose SHA-256 is in
machines.sha256. After the checks, every `<` in the posted comment is
replaced with U+FF1C `＜`, inside code and out, without parsing Markdown.
Thus `<` shows as `＜` in posted reviews, including in type applications,
and no literal HTML opener remains. This is distinct from Lean's `‹_›`
assumption notation. HTML tags are not refused; the replacement makes
them inert. If the review fails a check, the comment says why instead,
with the run's URL and no text of the review, and does not start with the
verdict's prefix, so that it counts as no review; the script then fails.
The resulting comment is checked again for loading content before
replacing `<`; it loads nothing from outside github.com, and no `@` in
it mentions anyone. The comment is written to its output file and is not
printed into the job's log, where its text could be a runner command.

The second form is the `review` job's, which holds the secrets, run before
the review leaves it: it fails if the review holds any of the values of
the environment variables SECRET_VAR, or of their distinctive parts, as
they are, reversed, in hexadecimal or in base64, whatever separates their
characters.
"""

import base64
import hashlib
import html
import os
import re
import sys

# The first line of a review: `Review of <full head sha>: VERDICT`, as
# AGENTS.md has a review start. The comment counts as the review of the
# head, for everything; `kind.py` reads it so too.
PREFIX = "Review of"

HERE = os.path.dirname(os.path.abspath(__file__))
# A finding: a list item of the top level, `N.` or `N)` after at most two
# spaces, whatever follows it (a nested item is indented further).
ITEM = re.compile(r"^ {0,2}\d+[.)]")
MARK = re.compile(r"\[(blocking|non-blocking(?:,[^\]]*)?)\]")
LOOSE_MARK = re.compile(r"\[(?:non-)?blocking[^\]]*\]")
TOKEN = re.compile(r"sk-ant-[\w-]{8,}|\bsk-[\w-]{16,}|\bgh[pousr]_[A-Za-z0-9]{20,}|\bgithub_pat_\w{20,}"
                   r"|\beyJ[A-Za-z0-9_-]{12,}\.[A-Za-z0-9_-]{12,}\.[A-Za-z0-9_-]{12,}")
URL = re.compile(r"\b(?:https?|ftp)://([^/\s)\]>\"'`]+)", re.IGNORECASE)
# A protocol-relative destination, `//host`, where Markdown takes one.
RELATIVE = re.compile(r"(?:^|[\s(<\[:=\"'])//([A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)+)")
# Any Markdown image (`![`, inline, full, collapsed or shortcut reference),
# even in code: images can load without `<`. HTML tags are made inert by
# replacing every `<` with `＜` in the posted comment, inside code and out,
# without parsing Markdown.
IMAGE = re.compile(r"!\[")
# The paragraph that says which probes the review ran (the probe job's)
# and which it could not, such as those that need a rebuild.
PROBES = re.compile(r"^[*_\s]*Probes[*_\s]*:", re.MULTILINE)


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


def loading(decoded):
    """Why the decoded text has a Markdown image or a link outside
    github.com, or None. HTML tags are neutralized in the posted body."""
    if IMAGE.search(decoded):
        return "it holds a Markdown image, which could load from elsewhere"
    if any(not github_host(h) for h in URL.findall(decoded) + RELATIVE.findall(decoded)):
        return "it links to a host other than github.com"
    return None


# An `@`, as itself or as an entity that Markdown decodes to one (`&#64;`,
# `&#x40;`, `&commat;`), before a login's character or another entity.
AT = re.compile(r"(?:@|&#0*64;|&#[xX]0*40;|&commat;)(?=[A-Za-z0-9_-]|&)")


def unmention(text):
    """`text` with every `@` before a login's character, plain or as an
    entity, made `@` and a zero-width space, so that the comment notifies
    no one. This holds in code too, where GitHub mentions no one, at the
    cost, which is deliberate, of an invisible character in such code as
    Lean's `@foo`: telling code from text needs a real CommonMark parse,
    and a guess at it once let a mention through."""
    return AT.sub("@\u200b", text)


def problem(text, head, kind):
    """What is wrong with the review, or None."""
    lines = text.splitlines()
    first = lines[0] if lines else ""
    # The reasons quote nothing of the review: the note that gives one is
    # posted unchecked.
    if first not in verdicts(head, kind):
        return "its first line is not a verdict that this review allows"
    # Markdown decodes entities, in a destination too (`h&#116;tps:`), so
    # the checks read the decoded text, applying it twice to catch
    # `&amp;#116;`.
    decoded = html.unescape(html.unescape(text))
    if TOKEN.search(decoded):
        return "it holds something that looks like a token"
    loads = loading(decoded)
    if loads:
        return loads
    blocking = False
    for number, line in enumerate(lines[1:], start=2):
        if not ITEM.match(line):
            continue
        marks = MARK.findall(line)
        if len(marks) != 1 or len(LOOSE_MARK.findall(line)) != 1:
            return f"the finding on its line {number} is not marked with exactly one of [blocking] and [non-blocking]"
        blocking |= marks[0] == "blocking"
    if blocking != first.endswith(": blocking issues"):
        return "its verdict does not agree with its [blocking] findings"
    # A clean verdict has no `[blocking]` mark anywhere, so a finding that
    # renders as one but escapes `ITEM` cannot hide under it.
    if not blocking and "blocking" in MARK.findall(decoded):
        return "it has a [blocking] mark under a clean verdict"
    if not PROBES.search(text):
        return "it has no `Probes:` paragraph saying which probes it ran and which it could not"
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
    """The comment to post, and whether the review passed. Whatever it is,
    the comment that leaves here loads nothing from outside github.com and
    mentions no one: the loading check runs on the comment as well as the
    review, before replacing every `<` with `＜`, inside code and out."""
    reason = problem(text, head, kind) if text else "it wrote no `review.md`"
    if reason is None:
        body, ok = scrub(text, names, hashes) + "\n", True
    else:
        body, ok = f"The `pr-review` workflow did not review {head}: {reason}. Its run is {run_url}.\n", False
    body = unmention(body)
    if loading(html.unescape(html.unescape(body))):
        body, ok = f"The `pr-review` workflow did not review {head}: see its run's log.\n", False
    # Replace every literal opener last, including in code and failure
    # notes. This needs no Markdown parse and leaves no `<` to open HTML.
    # Never decode the posted body: entity decoding is only for checks.
    return body.replace("<", "＜"), ok


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
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
