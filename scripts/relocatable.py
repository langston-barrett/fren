#!/usr/bin/env python3
"""Check that this build's outputs name no directory of the worktree.

    python3 scripts/relocatable.py --since FILE

Run it after `lake build --wfail`, with FILE a file touched just before
the build began, as the build jobs of `pre-merge` and `lean ci` do
(`Reqs/dev/Testing#shared-builds`). It reads each `.olean` and `.ilean`
file under `.lake/build/lib/lean`, and each file under `.lake/build/ir`
(C code and objects), that the build wrote, those modified after FILE,
and fails, listing them, if any contains the repository's root, with
symbolic links resolved as Lean sees it, followed by `/`. Outputs that
the build did not write are those of an earlier build, which was checked
when it wrote them, or are stale files of modules that this build no
longer has; either way, not this build's. Without `--since`, it reads
every output, which is right only after a build from an empty
`.lake/build`.

It checks Fren's own outputs only, not those of the dependencies in
`.lake/packages`: lean-smt's shared libraries keep the absolute install
name of the directory that built them, which nothing reads, since Lean
loads each of them by its path.
"""

import argparse
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--since", help="check only outputs modified after this file")
    a = p.parse_args()
    since = os.stat(a.since).st_mtime if a.since else None
    needle = (ROOT + "/").encode()
    build = os.path.join(ROOT, ".lake", "build")
    paths = []
    for d, _, files in os.walk(os.path.join(build, "lib", "lean")):
        paths += [os.path.join(d, f) for f in files if f.endswith((".olean", ".ilean"))]
    for d, _, files in os.walk(os.path.join(build, "ir")):
        # Lake's own records of a step, not its outputs.
        records = (".trace", ".hash", ".json", ".rsp")
        paths += [os.path.join(d, f) for f in files if not f.endswith(records)]
    checked, bad = 0, []
    for path in sorted(paths):
        if since is not None and os.stat(path).st_mtime <= since:
            continue
        checked += 1
        with open(path, "rb") as h:
            if needle in h.read():
                bad.append(os.path.relpath(path, ROOT))
    for b in sorted(bad):
        print(f"{b}: names the worktree's directory `{ROOT}`")
    print(f"relocatable: checked {checked} outputs, {len(bad)} name the worktree's directory")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
