#!/usr/bin/env python3
"""Check, before pushing, that the branch's new definitions are tested.

    python3 scripts/coverage_new.py [--base BASE]
    python3 scripts/coverage_new.py [--base BASE] --run JOB [ARG...] [--run JOB [ARG...]]...

`fren_coverage --new BASE` classifies each definition of `FrenCore`,
`FrenCoreCodes`, `Fren` and `FrenCli` that the working tree adds since its
merge base with BASE (`origin/main` by default) by the compiled code of
the executables (`Reqs/dev/Testing#coverage`):

- `UNREACHED`: no entry point reaches it: only proofs, `#guard`s,
  `#eval`s or `run_cmd`s use it, its callers inline it, or a `@[csimp]`
  replacement runs in its place. It needs no test.
- `DEAD`: nothing refers to it, not even a proof. Delete it.
- `REACHED`: it needs a test. Name the test in the pull request.

A definition is new if its name is on a line that `git diff` against the
merge base adds, or in a file that git does not track yet. Without
`--run`, that is all: it brings the `.olean` files that `fren_coverage`
reads up to date (`Fren` and every executable's root), which takes seconds
on a built worktree, and fails only on dead code. A normal build inlines
small functions, so it counts as reached what any reached definition uses.

With `--run`, it also checks that the tests named run the reached ones:
it builds `fren_test` with gcov's counters (`-Kcoverage`), using the
artifact cache, so only what changed is compiled again, clears the
counters, runs each `fren_test --job JOB ARG...`, and fails on a reached
definition that none of them ran and that `test/coverage.txt` does not
list. `main`'s `coverage` job, which runs the whole of `lake test`, stays
the backstop. The worktree's build is then the instrumented one, and
`lake -R build` returns to the normal one, from the artifact cache.

On macOS the profiling runtime is Apple's and the counters are read with
`xcrun llvm-cov gcov`; elsewhere set `COVERAGE_RUNTIME` and `LLVM_COV`, as
CI does. Builds and jobs run through `scripts/heavy`.
"""

import argparse
import glob
import os
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))


def heavy(cmd):
    """`cmd`, under the repository's `scripts/heavy`, or `heavy` on the
    `PATH`, if there is one."""
    own = os.path.join(ROOT, "scripts", "heavy")
    return ([own] if os.access(own, os.X_OK) else ["heavy"] if shutil.which("heavy") else []) + cmd


def run(cmd):
    print("+ " + " ".join(cmd), flush=True)
    return subprocess.run(cmd, cwd=ROOT).returncode


def toolchain():
    """The profiling runtime and the command that reads the counters."""
    runtime = os.environ.get("COVERAGE_RUNTIME")
    gcov = [os.environ["LLVM_COV"], "gcov"] if os.environ.get("LLVM_COV") else None
    if sys.platform == "darwin":
        found = sorted(glob.glob("/Library/Developer/CommandLineTools/usr/lib/clang/*/lib/darwin/libclang_rt.profile_osx.a"))
        runtime = runtime or (found[-1] if found else None)
        gcov = gcov or ["xcrun", "llvm-cov", "gcov"]
    if not runtime or not gcov:
        sys.exit("coverage_new: set COVERAGE_RUNTIME (LLVM's libclang_rt.profile) and LLVM_COV (its llvm-cov)")
    return runtime, gcov


def cache_dir():
    env = subprocess.run(["lake", "env", "printenv", "LAKE_CACHE_DIR"], cwd=ROOT,
                         capture_output=True, text=True, check=True)
    return env.stdout.strip()


# The libraries compiled with the counters (`lakefile.lean`), as paths
# under `.lake/build/ir`.
COUNTED = ("FrenCore", "FrenCoreCodes", "Fren", "FrenCli")


def stale_objects():
    """The objects of the counted libraries whose notes (`.gcno`) are not
    theirs: missing, or written by a later compile. The artifact cache gives
    back an object without its notes, which only compiling writes, together
    with the object: after `.lake/build` was deleted, or after an edit and
    its revert, the object is an earlier compile's."""
    stale = []
    ir = os.path.join(ROOT, ".lake", "build", "ir")
    for d, _, files in os.walk(ir):
        top = os.path.relpath(os.path.join(d, "x"), ir).split(os.sep)[0]
        for o in files:
            if ".c.o" not in o or o.endswith((".gcno", ".gcda", ".hash", ".trace", ".json", ".rsp")):
                continue
            module = o[: o.index(".c.o")]
            if (top if top != "x" else module) not in COUNTED:
                continue
            notes = os.path.join(d, module + ".c.o.gcno")
            path = os.path.join(d, o)
            if os.path.exists(notes):
                if os.stat(path).st_mtime < os.stat(notes).st_mtime - 2:
                    stale.append(path)
            else:
                # Only an object compiled with the counters names its
                # `.gcda`: an executable's root is compiled without them.
                with open(path, "rb") as h:
                    if b".gcda" in h.read():
                        stale.append(path)
    return stale


def exe_roots():
    """The root modules of `lakefile.lean`'s executables, whose `.olean`
    files `fren_coverage` reads: each `lean_exe`'s `root`, or its name."""
    roots, name = [], None
    with open(os.path.join(ROOT, "lakefile.lean")) as f:
        for line in f:
            decl = line.removeprefix("@[default_target] ")
            if decl.startswith("lean_exe "):
                if name:
                    roots.append(name)
                name = decl.split()[1]
            elif name and line.strip().startswith("root := `"):
                roots.append(line.strip().removeprefix("root := `"))
                name = None
            elif name and not line.startswith(" "):
                roots.append(name)
                name = None
    if name:
        roots.append(name)
    return roots


def evict(paths):
    """Delete the objects `paths` and their copies in the artifact cache,
    so that the next build compiles them again, with their notes. Only this
    worktree's builds use them (`-Kcoverage_dir`). The copies are found as
    the cache's own links to the objects: a cache on another filesystem
    copies its outputs instead, and then its copy cannot be found."""
    inodes = {(os.stat(p).st_dev, os.stat(p).st_ino): p for p in paths}
    evicted = set()
    for d, _, files in os.walk(os.path.join(cache_dir(), "artifacts")):
        for f in files:
            path = os.path.join(d, f)
            st = os.stat(path)
            if (st.st_dev, st.st_ino) in inodes:
                os.remove(path)
                evicted.add(inodes[(st.st_dev, st.st_ino)])
    missing = [p for p in paths if p not in evicted]
    if missing:
        sys.exit("coverage_new: the artifact cache keeps no link to "
                 + ", ".join(os.path.relpath(p, ROOT) for p in missing)
                 + " (it copies its outputs, as on another filesystem), so its copy cannot be evicted: "
                 "build without the cache, with `lake -R -Kcoverage=RUNTIME build fren_test` and no `-Kcoverage_dir`")
    for p in paths:
        os.remove(p)
        print(f"coverage_new: compiling {os.path.relpath(p, ROOT)} again, for its notes", flush=True)


def split_jobs(argv):
    """The jobs of `--run JOB ARG... --run JOB ARG...`."""
    jobs, rest = [], []
    for a in argv:
        if a == "--run":
            jobs.append([])
        elif jobs:
            jobs[-1].append(a)
        else:
            rest.append(a)
    if any(not j for j in jobs):
        sys.exit("coverage_new: `--run` needs a job")
    return jobs, rest


def main():
    jobs, rest = split_jobs(sys.argv[1:])
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--base", default="origin/main", help="the branch's base (default: origin/main)")
    a = p.parse_args(rest)
    # Every executable's root, and `Fren`, which `fren_coverage` reads, so
    # that none of their `.olean` files is stale.
    targets = ["Fren", *exe_roots(), "fren_coverage"]
    if not jobs:
        if run(heavy(["lake", "build", *targets])) != 0:
            sys.exit("coverage_new: the build failed")
        sys.exit(run(["lake", "exe", "fren_coverage", "--static", "--new", a.base]))
    runtime, gcov = toolchain()
    # `-Kcoverage_dir` puts the worktree's directory in the key of each
    # object in the artifact cache, since the object writes its counters
    # there (`lakefile.lean`).
    k = [f"-Kcoverage={runtime}", f"-Kcoverage_dir={ROOT}"]
    build = heavy(["lake", "-R", *k, "build", "fren_test", *targets])
    if run(build) != 0:
        sys.exit("coverage_new: the instrumented build failed")
    stale = stale_objects()
    if stale:
        evict(stale)
        if run(build) != 0 or stale_objects():
            sys.exit("coverage_new: the instrumented build failed")
    for d, _, files in os.walk(os.path.join(ROOT, ".lake", "build")):
        for f in files:
            if f.endswith(".gcda"):
                os.remove(os.path.join(d, f))
    failed = False
    for job in jobs:
        out = subprocess.run(heavy(["lake", *k, "env", ".lake/build/bin/fren_test", "--job", *job]),
                             cwd=ROOT, capture_output=True, text=True)
        print(f"job {' '.join(job)}: exit {out.returncode}, {out.stdout.strip()[:2000]}", flush=True)
        failed |= out.returncode != 0 or out.stdout.strip() != "[]"
    code = run(["lake", *k, "exe", "fren_coverage", "--new", a.base, *gcov])
    if failed:
        print("coverage_new: a job failed", file=sys.stderr)
    sys.exit(code or (1 if failed else 0))


if __name__ == "__main__":
    main()
