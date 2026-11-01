#!/usr/bin/env python3
"""One-off migration for #509: format ui fixtures and keep their annotations.

    python3 -I scripts/migrations/fmt_ui_annotations.py FREN FILE...

For each FILE, a ui test (`src/FrenTest/Ui.lean`), this runs `FREN fmt` on it
and then moves each `--~` annotation to the line where its message now
starts, keeping its text:

- The binary's messages (`FREN check FILE`) give where each annotated message
  starts, a line and column: each annotation, in order, takes the first
  message left on its line, by column, that meets it. Where none does (an
  annotation for the Lean front end alone, or a `--~?`), it stands for the
  first token of the line that it names.
- `fren fmt` keeps every token and comment, and adds or removes only trailing
  commas, so lining up the text outside comments and whitespace before and
  after formatting maps that position to its new line.
- An annotation is in place when it is still as far below the line that it
  names as it was, or still at the end of that line. Every annotation of a
  line where one is not is placed anew: the first at the end of that line,
  where the line has no comment, and the others on lines of their own just
  below it, with one caret, two, and so on.
- A comment inside a construct can change a lint's message (a fix that
  would drop it is not offered). Where placing a line's annotations anew
  changes the binary's messages, they stay where `fren fmt` put them, after
  the same token as before, each on a line of its own, with as many carets
  as it now needs.

Afterwards it checks that formatting the file changes nothing, that each
annotation names the line where its message starts, and that the binary's
messages are the same, apart from their positions, and each on the line
where its old position maps to. The ui job (`fren_test --job ui FILE...`)
then checks both front ends against the annotations, and
`compare_ui_messages.py` compares both front ends' messages before and
after.

It prints one line for each file, and exits 1 if any check failed.
"""

import collections
import difflib
import re
import subprocess
import sys


def lex(src):
    """The significant characters of `src`, outside whitespace and comments,
    as (offset, char), and the comments' spans, as (start, stop)."""
    sig, comments = [], []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c.isspace():
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            comments.append((i, j))
            i = j
        elif src.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            comments.append((i, j))
            i = j
        elif c == "r" and src[i + 1 : i + 2] in ('"', "#") and not (i and (src[i - 1].isalnum() or src[i - 1] in "_?!")):
            j = i + 1
            while src[j] == "#":
                j += 1
            close = '"' + "#" * (j - i - 1)
            stop = src.index(close, j + 1) + len(close)
            sig += [(k, src[k]) for k in range(i, stop) if not src[k].isspace()]
            i = stop
        elif c == '"':
            j = i + 1
            while src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            sig += [(k, src[k]) for k in range(i, j + 1) if not src[k].isspace()]
            i = j + 1
        else:
            sig.append((i, c))
            i += 1
    return sig, comments


class Text:
    def __init__(self, src):
        self.src = src
        self.starts = [0] + [m.end() for m in re.finditer("\n", src)]

    def line_of(self, offset):
        lo, hi = 0, len(self.starts) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if self.starts[mid] <= offset:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1

    def offset(self, line, col):
        return self.starts[line - 1] + col


ANN = re.compile(r"--~(\$?)(\^*)(.*)", re.S)


def annotations(text, comments):
    """Each annotation: its comment's span, line, whether it is alone on its
    line, its `$`, its number of carets and the rest of its text."""
    out = []
    for a, b in comments:
        body = text.src[a:b]
        k = body.find("--~")
        if k < 0:
            continue
        m = ANN.match(body, k)
        line = text.line_of(a)
        alone = text.src[text.starts[line - 1] : a].strip() == ""
        out.append(dict(span=(a, b), line=line, alone=alone, prefix=body[:k], dollar=m.group(1),
                        carets=len(m.group(2)), rest=m.group(3)))
    return out


def parse_rest(rest):
    rest = rest[1:] if rest.startswith("?") else rest
    if rest.startswith("["):
        rest = rest[rest.index("]") + 1 :]
    rest = rest.strip()
    for sev in ("error", "warning", "info"):
        if rest.startswith(sev + ": "):
            return sev, rest[len(sev) + 2 :].strip()
    raise ValueError(f"bad annotation {rest!r}")


HEADER = re.compile(r"^(error|warning|note)(?:\[(\w+)\])?: (.*)$")


def diagnostics(fren, path):
    """The binary's messages about `path`: (severity, code, text, line, col),
    with col from 0, as `FrenTest.Ui.cliDiagnostics` reads them."""
    out = subprocess.run([fren, "check", "--color", "never", path], capture_output=True, text=True)
    diags, cur, note_at = [], None, None
    for line in (out.stdout + out.stderr).split("\n"):
        t = line.strip()
        m = HEADER.match(line)
        if m:
            sev = {"note": "info"}.get(m.group(1), m.group(1))
            cur = dict(sev=sev, code=m.group(2), text=m.group(3), line=0, col=0, pending=True)
            diags.append(cur)
        elif t.startswith("--> ") and cur and cur["pending"]:
            loc = t[4:].rsplit(":", 2)
            if loc[0] == path:
                cur["line"], cur["col"] = int(loc[1]), int(loc[2]) - 1
            cur["pending"] = False
        elif line.startswith("fren: "):
            cur = None
        elif cur and t.startswith("= "):
            cur["text"] += "\n" + t[2:]
    return [(d["sev"], d["code"], d["text"], d["line"], d["col"]) for d in diags]


def fmt(fren, path):
    subprocess.run([fren, "fmt", path], check=True)
    with open(path) as f:
        return f.read()


def position_map(sig0, sig1):
    """Index in `sig0` to index in `sig1`, where the characters match."""
    sm = difflib.SequenceMatcher(None, [c for _, c in sig0], [c for _, c in sig1], autojunk=False)
    m = {}
    for a, b, size in sm.get_matching_blocks():
        for k in range(size):
            m[a + k] = b + k
    return m


def new_line_of(t0, sig0, t1, sig1, pmap, line, col):
    """The new line of the first significant character at or after (line,
    col), on that line."""
    off = t0.offset(line, col)
    for k, (o, _) in enumerate(sig0):
        if o >= off and t0.line_of(o) == line:
            if k not in pmap:
                raise ValueError(f"line {line}:{col + 1}: its token did not survive formatting")
            return t1.line_of(sig1[pmap[k]][0])
    raise ValueError(f"line {line}:{col + 1}: no token there")


def migrate(fren, path):
    with open(path) as f:
        src0 = f.read()
    t0 = Text(src0)
    sig0, com0 = lex(src0)
    anns0 = annotations(t0, com0)
    diags0 = diagnostics(fren, path)
    # Where each annotation's message starts, before formatting.
    targets, taken = [], set()
    for a in anns0:
        if a["dollar"]:
            targets.append(None)
            continue
        line = a["line"] - a["carets"]
        sev, text = parse_rest(a["rest"])
        # The first message left on the line, by column, that meets it.
        meeting = sorted((d[4], k) for k, d in enumerate(diags0)
                         if k not in taken and d[3] == line and d[0] == sev and text in d[2])
        if meeting:
            taken.add(meeting[0][1])
            col = meeting[0][0]
        else:
            col = len(t0.src[t0.starts[line - 1] :]) - len(t0.src[t0.starts[line - 1] :].lstrip(" "))
        targets.append((line, col))

    src1 = fmt(fren, path)
    t1 = Text(src1)
    sig1, com1 = lex(src1)
    anns1 = annotations(t1, com1)
    assert [a["prefix"] + a["rest"] for a in anns0] == [a["prefix"] + a["rest"] for a in anns1], "annotations changed"
    pmap = position_map(sig0, sig1)
    # The new line that each annotation names.
    new_targets = [new_line_of(t0, sig0, t1, sig1, pmap, *tgt) if tgt else None for tgt in targets]

    def in_place(a0, a1, t):
        if a1["alone"]:
            return a0["alone"] and a1["line"] - t == a0["carets"]
        return a1["line"] == t and a0["carets"] == 0

    moved = sorted({t for a0, a1, t in zip(anns0, anns1, new_targets) if t is not None and not in_place(a0, a1, t)})

    def build(anew_lines):
        """The text, with the annotations of `anew_lines` placed anew, and
        those of the other moved lines below where `fren fmt` put them."""
        dropped, stripped = set(), {}
        anew, below = collections.defaultdict(list), collections.defaultdict(list)
        for a, t in zip(anns1, new_targets):
            if t not in moved:
                continue
            if a["prefix"]:
                raise ValueError(f"line {a['line']}: the annotation follows another comment")
            if t in anew_lines:
                anew[t].append(a)
            elif a["alone"]:
                continue
            else:
                below[a["line"]].append(a)
            if a["alone"]:
                dropped.add(a["line"])
            else:
                line = src1.split("\n")[a["line"] - 1]
                stripped[a["line"]] = line[: a["span"][0] - t1.starts[a["line"] - 1]].rstrip()
        # The new text, as lines of code, by their old number, and
        # annotations on lines of their own, by the old line they name.
        out = []
        for i, line in enumerate(src1.split("\n"), 1):
            if i in dropped:
                continue
            own = [(a, t) for a, t in zip(anns1, new_targets) if a["alone"] and a["line"] == i and t is not None]
            if own:
                a, t = own[0]
                out.append(("ann", t, line[: a["span"][0] - t1.starts[i - 1]] + a["prefix"], a["rest"]))
                continue
            line = stripped.get(i, line)
            anns = anew.get(i, [])
            if anns and not lex(line)[1]:
                line += "  --~" + anns[0]["rest"]
                anns = anns[1:]
            out.append(("code", i, line))
            indent = line[: len(line) - len(line.lstrip(" "))]
            out += [("ann", i, indent, a["rest"]) for a in anns]
            out += [("ann", t, indent, a["rest"]) for a, t in zip(anns1, new_targets) if a in below.get(i, [])]
        where = {e[1]: k + 1 for k, e in enumerate(out) if e[0] == "code"}
        return "\n".join(e[2] if e[0] == "code" else e[2] + "--~" + "^" * (k + 1 - where[e[1]]) + e[3]
                         for k, e in enumerate(out))

    key = lambda d: (d[0], d[1] or "", d[2])

    def same_messages(src):
        with open(path, "w") as f:
            f.write(src)
        return sorted(map(key, diagnostics(fren, path))) == sorted(map(key, diags0))

    # Place anew every moved line's annotations whose placing anew keeps the
    # messages, or, if together they do not, none.
    anew_lines = set(moved)
    if not same_messages(build(anew_lines)):
        anew_lines = {t for t in moved if same_messages(build({t}))}
        if not same_messages(build(anew_lines)):
            anew_lines = set()
    src2 = build(anew_lines)
    with open(path, "w") as f:
        f.write(src2)
    src3 = fmt(fren, path)
    if fmt(fren, path) != src3:
        raise ValueError("formatting the migrated file is not idempotent")

    # Each annotation names the line where its message now starts.
    t3 = Text(src3)
    sig3, com3 = lex(src3)
    pmap3 = position_map(sig0, sig3)
    want = sorted((new_line_of(t0, sig0, t3, sig3, pmap3, *tgt) if tgt else 0, a["rest"])
                  for a, tgt in zip(anns0, targets))
    have = sorted((0 if a["dollar"] else a["line"] - a["carets"], a["rest"]) for a in annotations(t3, com3))
    if want != have:
        raise ValueError("an annotation names another line than where its message starts")

    # The binary's messages are the same, and each is where its old
    # position maps to.
    diags1 = diagnostics(fren, path)
    if sorted(map(key, diags0)) != sorted(map(key, diags1)):
        raise ValueError("the binary's messages differ:\n" + "\n".join(difflib.unified_diff(
            sorted(f"{key(d)}" for d in diags0), sorted(f"{key(d)}" for d in diags1), lineterm="")))
    expected = sorted((key(d), new_line_of(t0, sig0, t3, sig3, pmap3, d[3], d[4]) if d[3] else 0) for d in diags0)
    got = sorted((key(d), d[3]) for d in diags1)
    if expected != got:
        raise ValueError("a message of the binary moved to another line than its token")
    n_anew = sum(1 for t in new_targets if t in anew_lines)
    n_below = sum(1 for t in new_targets if t in moved and t not in anew_lines)
    return len(anns0), len(diags0), n_anew, n_below


def main():
    fren, files = sys.argv[1], sys.argv[2:]
    ok = True
    for path in files:
        try:
            n, d, anew, below = migrate(fren, path)
            print(f"{path}: {n} annotations, {d} messages of the binary; {anew} placed anew, {below} left below")
        except Exception as e:  # noqa: BLE001
            ok = False
            print(f"{path}: FAILED: {e}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
