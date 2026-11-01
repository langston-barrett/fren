#!/usr/bin/env python3
"""Checks #509's migration of ui fixtures against both front ends.

    python3 -I scripts/migrations/compare_ui_messages.py FREN_TEST OLD_DIR FILE...

OLD_DIR holds a copy of each FILE as it was before `fmt_ui_annotations.py`
ran, at the same relative path. For the old and the new text of each FILE,
this runs the ui job (`FREN_TEST --job ui`, under `lake env`) on it with
every annotation turned into a plain comment (`--~` to `-- ~`), so that
every message of either front end is reported as unexpected, with its line.
It then checks that each front end gives the same messages, by severity and
text, before and after, and that each is on a line that holds a token of
the line it was on before. It restores each FILE afterwards.
"""

import collections
import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fmt_ui_annotations import Text, lex, position_map  # noqa: E402

UNEXPECTED = re.compile(r"^(.*) \((binary|Lean)\): line (\d+): unexpected (error|warning|info): (.*)$", re.S)


def messages(fren_test, files, texts):
    """Each front end's messages about each file, as {file: [(front end,
    line, severity, text)]}, with the files' texts set to `texts`."""
    for f, t in zip(files, texts):
        with open(f, "w") as h:
            h.write(t.replace("--~", "-- ~"))
    out = subprocess.run(["lake", "env", fren_test, "--job", "ui", *files], capture_output=True, text=True)
    res = collections.defaultdict(list)
    for e in json.loads(out.stdout):
        m = UNEXPECTED.match(e)
        if m:
            res[m.group(1)].append((m.group(2), int(m.group(3)), m.group(4), m.group(5)))
    return res


def lines_of(t0, sig0, t1, sig1, pmap):
    """For each old line, the new lines that its tokens are on."""
    out = collections.defaultdict(set)
    for k, (o, _) in enumerate(sig0):
        if k in pmap:
            out[t0.line_of(o)].add(t1.line_of(sig1[pmap[k]][0]))
    return out


def main():
    fren_test, old_dir, files = sys.argv[1], sys.argv[2], sys.argv[3:]
    old = [open(os.path.join(old_dir, f)).read() for f in files]
    new = [open(f).read() for f in files]
    try:
        before = messages(fren_test, files, old)
        after = messages(fren_test, files, new)
    finally:
        for f, t in zip(files, new):
            with open(f, "w") as h:
                h.write(t)
    ok = True
    for f, s0, s1 in zip(files, old, new):
        b, a = before.get(f, []), after.get(f, [])
        t0, t1 = Text(s0), Text(s1)
        sig0, _ = lex(s0)
        sig1, _ = lex(s1)
        where = lines_of(t0, sig0, t1, sig1, position_map(sig0, sig1))
        key = lambda m: (m[0], m[2], m[3])
        problems = []
        if sorted(map(key, b)) != sorted(map(key, a)):
            problems.append("the messages differ")
        else:
            # Each message is on one of the new lines of its old line, given
            # in order among those alike.
            olds = collections.defaultdict(list)
            for m in sorted(b):
                olds[key(m)].append(m[1])
            news = collections.defaultdict(list)
            for m in sorted(a):
                news[key(m)].append(m[1])
            for k, ls in olds.items():
                for l0, l1 in zip(ls, news[k]):
                    if (l0 == 0) != (l1 == 0) or (l0 and l1 not in where[l0]):
                        problems.append(f"{k[0]}: a message on line {l0} is now on line {l1}")
        counts = collections.Counter(m[0] for m in b)
        summary = ", ".join(f"{counts[fe]} of {fe}" for fe in ("binary", "Lean"))
        print(f"{f}: {summary}: {'; '.join(problems) if problems else 'same messages, on the same tokens'}")
        ok = ok and not problems
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
