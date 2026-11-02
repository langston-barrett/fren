#!/usr/bin/env python3
"""The size of Lake's artifact cache, and pruning it.

    python3 scripts/lake_cache.py size
    heavy python3 scripts/lake_cache.py prune [--days N] [--grace SECONDS]

The cache is the one that the repository's builds use: `LAKE_CACHE_DIR`
if set, otherwise `lake/cache` in the toolchain's directory, as Lake has
it (`lake env`). It only grows: each build adds the outputs of every step
that it runs, and each build's `.lake/build` links to them, so deleting a
worktree's `.lake` frees nothing until the cache lets go of them too
(`Reqs/dev/Testing#shared-builds`).

`size` prints how much the cache holds, and how much of it no worktree
links to, which pruning can free.

`prune` deletes the artifacts that no worktree's `.lake/build` links to
(a link count of 1) and that no build has linked or unlinked for `--days`
days (by the time of the last change to their links, `ctime`; default 7),
and every entry of the cache that names one of them. It deletes the
entries first, then waits `--grace` seconds (default 60), then deletes
each artifact that still has no other link. A build that finds a step's
entry gone runs the step, so entries go first; one that read an entry
before it went links the artifact within the grace, and the check of the
link count then keeps it. An entry that names an artifact already gone,
which would make a build warn and so fail `--wfail`, is deleted too. Run
it under `heavy`, so that no build of the machine's other agents starts
while it runs, as long as `heavy` has one slot; with more, the grace and
the second check are what keeps a build from losing an artifact.
"""

import argparse
import json
import os
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def cache_dir():
    env = subprocess.run(["lake", "env", "printenv", "LAKE_CACHE_DIR"], cwd=ROOT,
                         capture_output=True, text=True, check=True)
    return env.stdout.strip()


def gib(n):
    return f"{n / 2**30:.2f} GiB"


def artifacts_of(entry):
    """The artifacts that an entry of `outputs/` names."""
    try:
        data = json.load(open(entry)).get("data")
    except (OSError, ValueError):
        return None
    names = []

    def walk(v):
        if isinstance(v, str):
            names.append(v)
        elif isinstance(v, list):
            for x in v:
                walk(x)
        elif isinstance(v, dict):
            for x in v.values():
                walk(x)

    walk(data)
    return names


def scan(cache):
    arts = {}
    adir = os.path.join(cache, "artifacts")
    if os.path.isdir(adir):
        for f in os.listdir(adir):
            st = os.stat(os.path.join(adir, f))
            arts[f] = st
    entries = []
    odir = os.path.join(cache, "outputs")
    for d, _, fs in os.walk(odir):
        entries += [os.path.join(d, f) for f in fs if f.endswith(".json")]
    return adir, arts, entries


def size(cache):
    _, arts, entries = scan(cache)
    total = sum(st.st_size for st in arts.values())
    free = sum(st.st_size for st in arts.values() if st.st_nlink == 1)
    print(f"{cache}: {len(arts)} artifacts, {gib(total)}; {len(entries)} entries; "
          f"{gib(free)} in artifacts that no worktree links to")


def prune(cache, days, grace):
    adir, arts, entries = scan(cache)
    cutoff = time.time() - days * 86400
    old = {f for f, st in arts.items() if st.st_nlink == 1 and st.st_ctime < cutoff}
    dropped = 0
    for e in entries:
        names = artifacts_of(e)
        if names is None or any(n in old or n not in arts for n in names):
            os.remove(e)
            dropped += 1
    print(f"deleted {dropped} of {len(entries)} entries; waiting {grace} s", flush=True)
    time.sleep(grace)
    freed, n = 0, 0
    for f in old:
        path = os.path.join(adir, f)
        try:
            st = os.stat(path)
        except FileNotFoundError:
            continue
        if st.st_nlink == 1:
            os.remove(path)
            freed += st.st_size
            n += 1
    print(f"deleted {n} artifacts, {gib(freed)}")


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="mode", required=True)
    sub.add_parser("size")
    q = sub.add_parser("prune")
    q.add_argument("--days", type=float, default=7)
    q.add_argument("--grace", type=float, default=60)
    a = p.parse_args()
    cache = cache_dir()
    if not os.path.isdir(cache):
        print(f"{cache}: no cache yet")
        return
    if a.mode == "size":
        size(cache)
    else:
        prune(cache, a.days, a.grace)
        size(cache)


if __name__ == "__main__":
    sys.exit(main())
