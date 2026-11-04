#!/usr/bin/env python3
"""Checks #669's `require` migration against both front ends.

    python3 -I scripts/migrations/compare_require.py capture OUT.json FREN_TEST FILE...
    python3 -I scripts/migrations/compare_require.py compare OLD.json NEW.json

`capture` runs the ui job (`FREN_TEST --job ui`, under `lake env`) on each
FILE with every annotation turned into a plain comment (`--~` to `-- ~`),
so that every message of either front end is reported as unexpected, with
its line, and writes the job's failures, by file, to OUT.json. It restores
each FILE afterwards. Run it before the migration, with the binaries and
the files as they were, and after it, with both as they are.

`compare` prints each failure that is in one capture and not in the
other, and fails unless they differ only in the keyword: once `require`
is read as `assume` in both, and "a `require`" as "an `assume`", every
file's failures must be the same. The
migration rewrites `assume` as `require` on the same line, so the lines of
the messages stay as they were.
"""

import json
import re
import subprocess
import sys


def capture(out, fren_test, files):
    texts = [open(f).read() for f in files]
    try:
        for f, t in zip(files, texts):
            with open(f, "w") as h:
                h.write(t.replace("--~", "-- ~"))
        res = {f: [] for f in files}
        for k in range(0, len(files), BATCH):
            batch = files[k : k + BATCH]
            run = subprocess.run(["lake", "env", fren_test, "--job", "ui", *batch], capture_output=True, text=True)
            try:
                failures = json.loads(run.stdout.strip().splitlines()[-1])
            except (json.JSONDecodeError, IndexError):
                failures = [f"the ui job exited {run.returncode} without a list of failures: {run.stdout}{run.stderr}"]
            for e in failures:
                # The file that the failure is about, the longest that it
                # starts with.
                named = [f for f in batch if e.startswith(f + ":") or e.startswith(f + " (")]
                key = max(named, key=len) if named else f"{batch[0]}..."
                res.setdefault(key, []).append(e)
            print(f"{k + len(batch)} of {len(files)}", file=sys.stderr)
        res = {f: sorted(v) for f, v in res.items()}
    finally:
        for f, t in zip(files, texts):
            with open(f, "w") as h:
                h.write(t)
    with open(out, "w") as h:
        json.dump(res, h, indent=1, sort_keys=True)


BATCH = 40

KEYWORD = re.compile(r"\brequire(s?)\b")


def same_but_keyword(e):
    """`e` with `require` read as `assume`, and its article with it."""
    return KEYWORD.sub(r"assume\1", e.replace("a `require`", "an `assume`"))


def compare(old_path, new_path):
    old, new = json.load(open(old_path)), json.load(open(new_path))
    ok = True
    changed = 0
    for f in sorted(set(old) | set(new)):
        a, b = old.get(f), new.get(f)
        if a is None or b is None:
            print(f"{f}: only {'after' if a is None else 'before'}")
            ok = False
            continue
        if a == b:
            continue
        gone = [e for e in a if e not in b]
        came = [e for e in b if e not in a]
        for e in gone:
            print(f"- {e}")
        for e in came:
            print(f"+ {e}")
        if sorted(map(same_but_keyword, a)) != sorted(map(same_but_keyword, b)):
            print(f"{f}: the messages differ beyond the keyword")
            ok = False
        else:
            changed += 1
    n = sum(len(v) for v in old.values())
    print(f"{len(old)} files, {n} failures before; {changed} files differ only in the keyword; {'ok' if ok else 'NOT OK'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    if sys.argv[1] == "capture":
        capture(sys.argv[2], sys.argv[3], sys.argv[4:])
    else:
        compare(sys.argv[2], sys.argv[3])
