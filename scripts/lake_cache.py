#!/usr/bin/env python3
"""The size of Lake's artifact cache, and pruning it.

    python3 scripts/lake_cache.py size [--cache DIR]
    scripts/heavy python3 scripts/lake_cache.py prune [--days N] [--grace SECONDS]
        [--cache DIR]
    python3 scripts/lake_cache.py test

The cache is the one that the repository's builds use: `LAKE_CACHE_DIR`
if set, otherwise `lake/cache` in the toolchain's directory, as Lake has
it (`lake env`), or `--cache DIR`. There is one for each toolchain, so
after a toolchain bump the old toolchain's cache stays until it is pruned
with `--cache` or deleted by hand, once no worktree builds with that
toolchain. It only grows: each build adds the outputs of every step that
it runs, and each build's `.lake/build` links to them, so deleting a
worktree's `.lake` frees nothing until the cache lets go of them too
(`Reqs/dev/Testing#shared-builds`).

Link counts tell which artifacts a worktree uses only when the worktree
and the cache are on one filesystem: across filesystems, Lake copies
instead of linking, every artifact has a link count of 1, and the
worktree's outputs take disk twice. Both commands check that the
worktree that runs them is on the cache's filesystem, and `prune` refuses
otherwise. They check only that worktree: another one on another
filesystem holds copies, which pruning leaves alone, but they count as no
link, so the entries of its steps may be pruned, and a build that would
take them from the cache runs them again.

`size` prints how much the cache holds, and how much of it no worktree
links to, which pruning can free.

`prune` deletes the artifacts that no worktree's `.lake/build` links to
(a link count of 1) and whose links have not changed for `--days` days
(by `ctime`; default 7), and every entry of the cache that names one of
them. It scans the entries before the artifacts, so that an entry written
between the two scans names an artifact that the second scan sees. It
deletes the entries first, then waits `--grace` seconds (default 60),
then deletes each artifact whose link count is still 1 and whose `ctime`
is still the one scanned. A build that finds a step's entry gone runs the
step and saves its outputs again; Lake then changes the artifact's access
rights, or links it, either of which changes its `ctime`, so the second
check keeps an artifact that a build used or saved again during the
grace, all but one that a build links in the microseconds between that
check and the deletion. An entry that names an artifact already gone, or that cannot be
read, which would make a build warn and so fail `--wfail`, is deleted
too. Run it under `scripts/heavy`, so that fewer builds run while it does.

`test` runs the checks of `prune` on a scratch cache.
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))


def cache_dir():
    env = subprocess.run(["lake", "env", "printenv", "LAKE_CACHE_DIR"], cwd=ROOT,
                         capture_output=True, text=True, check=True)
    return env.stdout.strip()


def gib(n):
    return f"{n / 2**30:.2f} GiB"


def stat_or_none(path):
    try:
        return os.stat(path)
    except FileNotFoundError:
        return None


def remove(path):
    try:
        os.remove(path)
        return True
    except FileNotFoundError:
        return False


def artifacts_of(entry):
    """The artifacts that an entry of `outputs/` names, or None if it cannot
    be read."""
    try:
        with open(entry) as f:
            top = json.load(f)
    except (OSError, ValueError):
        return None
    if not isinstance(top, dict):
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

    walk(top.get("data"))
    return names


def scan(cache):
    """The entries, then the artifacts with their `stat`s."""
    entries = []
    for d, _, fs in os.walk(os.path.join(cache, "outputs")):
        entries += [os.path.join(d, f) for f in fs if f.endswith(".json")]
    adir = os.path.join(cache, "artifacts")
    arts = {}
    if os.path.isdir(adir):
        for f in os.listdir(adir):
            st = stat_or_none(os.path.join(adir, f))
            if st is not None:
                arts[f] = st
    return adir, arts, entries


def same_filesystem(cache, root=ROOT):
    return os.stat(cache).st_dev == os.stat(root).st_dev


def size(cache):
    _, arts, entries = scan(cache)
    total = sum(st.st_size for st in arts.values())
    free = sum(st.st_size for st in arts.values() if st.st_nlink == 1)
    print(f"{cache}: {len(arts)} artifacts, {gib(total)}; {len(entries)} entries; "
          f"{gib(free)} in artifacts that no worktree links to")
    if not same_filesystem(cache):
        print(f"warning: {ROOT} is not on the cache's filesystem, so Lake copies its outputs "
              "and the link counts say nothing")


def prune(cache, days, grace, between=None):
    adir, arts, entries = scan(cache)
    cutoff = time.time() - days * 86400
    old = {f: st for f, st in arts.items() if st.st_nlink == 1 and st.st_ctime < cutoff}
    dropped = 0
    for e in entries:
        names = artifacts_of(e)
        if names is None or any(n in old or n not in arts for n in names):
            dropped += remove(e)
    print(f"deleted {dropped} of {len(entries)} entries; waiting {grace} s", flush=True)
    if between is not None:
        between()
    time.sleep(grace)
    freed, n = 0, 0
    for f, was in old.items():
        path = os.path.join(adir, f)
        st = stat_or_none(path)
        if st is not None and st.st_nlink == 1 and st.st_ctime == was.st_ctime and remove(path):
            freed += st.st_size
            n += 1
    print(f"deleted {n} artifacts, {gib(freed)}")


def test():
    """`prune` keeps an artifact that is saved again or linked during the
    grace, deletes an old unlinked one with its entry, and deletes entries
    that cannot be read or that name a missing artifact."""
    with tempfile.TemporaryDirectory() as cache:
        art, out = os.path.join(cache, "artifacts"), os.path.join(cache, "outputs", "fren")
        os.makedirs(art)
        os.makedirs(out)
        for name in ["kept.olean", "linked.olean", "gone.olean"]:
            with open(os.path.join(art, name), "w") as f:
                f.write(name)
            os.chmod(os.path.join(art, name), 0o444)
        entries = {
            "kept": {"data": {"o": ["kept.olean"]}},
            "linked": {"data": "linked.olean"},
            "gone": {"data": {"o": ["gone.olean"], "m": False}},
            "missing": {"data": "missing.olean"},
            "list": ["not", "an", "object"],
        }
        for k, v in entries.items():
            with open(os.path.join(out, k + ".json"), "w") as f:
                json.dump(v, f)
        with open(os.path.join(out, "bad.json"), "w") as f:
            f.write("{")
        time.sleep(0.05)

        def between():
            # A build saves `kept` again (Lake sets its access rights) and
            # another links `linked` into its `.lake/build`.
            os.chmod(os.path.join(art, "kept.olean"), 0o444)
            os.link(os.path.join(art, "linked.olean"), os.path.join(cache, "worktree.olean"))

        prune(cache, 0, 0.05, between)
        left = sorted(os.listdir(art))
        assert left == ["kept.olean", "linked.olean"], left
        assert sorted(os.listdir(out)) == [], sorted(os.listdir(out))
        assert same_filesystem(cache, cache)
    print("lake_cache: test passed")


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="mode", required=True)
    s = sub.add_parser("size")
    s.add_argument("--cache")
    q = sub.add_parser("prune")
    q.add_argument("--days", type=float, default=7)
    q.add_argument("--grace", type=float, default=60)
    q.add_argument("--cache")
    sub.add_parser("test")
    a = p.parse_args()
    if a.mode == "test":
        test()
        return 0
    cache = a.cache or cache_dir()
    if not os.path.isdir(cache):
        print(f"{cache}: no cache yet")
        return 0
    if a.mode == "size":
        size(cache)
        return 0
    if not same_filesystem(cache):
        print(f"{ROOT} is not on the cache's filesystem, so link counts say nothing; not pruning")
        return 2
    prune(cache, a.days, a.grace)
    size(cache)
    return 0


if __name__ == "__main__":
    sys.exit(main())
