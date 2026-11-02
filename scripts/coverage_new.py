#!/usr/bin/env python3
"""Check, before pushing, that the branch's new definitions are tested.

    python3 scripts/coverage_new.py [--base BASE]
    python3 scripts/coverage_new.py [--base BASE] --run JOB [ARG...] [--run JOB [ARG...]]...

`fren_coverage --new BASE` classifies each definition of `FrenCore`,
`FrenCoreCodes`, `Fren` and `FrenCli` that the working tree adds since its
merge base with BASE (`origin/main` by default) by the compiled code of
the executables (`Reqs/dev/Testing#coverage`):

- `UNREACHED`: no compiled entry point reaches it, so only proofs,
  `#guard`s, `#eval`s or Lean's interpreter use it. It needs no test.
- `DEAD`: nothing refers to it, not even a proof. Delete it.
- `REACHED`: it needs a test. Name the test in the pull request.

Without `--run`, that is all: it reads the build that the worktree has, in
seconds, and fails only on dead code. A normal build inlines small
functions, so it counts as reached what any reached definition uses.

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
CI does. Builds and jobs run through `heavy` when it is on the `PATH`.
"""

import argparse
import glob
import os
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))


def heavy(cmd):
    """`cmd`, under `heavy` if there is one."""
    return (["heavy"] if shutil.which("heavy") else []) + cmd


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


def stale_objects():
    """The objects that the artifact cache gave back for notes (`.gcno`)
    that a later compile wrote: an object written by an earlier compile of
    the module, as after an edit and its revert. Compiling writes the
    notes and the object together."""
    stale = []
    for d, _, files in os.walk(os.path.join(ROOT, ".lake", "build", "ir")):
        for f in files:
            if not f.endswith(".c.o.gcno"):
                continue
            notes = os.stat(os.path.join(d, f)).st_mtime
            base = f[: -len(".gcno")]
            for o in files:
                path = os.path.join(d, o)
                if o.startswith(base + ".") and o.endswith(("export", ".o")) or o == base:
                    if os.stat(path).st_mtime < notes - 2:
                        stale.append(path)
    return stale


def evict(paths):
    """Delete the objects `paths` and their copies in the artifact cache,
    so that the next build compiles them again, with their notes. Only this
    worktree's builds use them (`-Kcoverage_dir`)."""
    inodes = {(os.stat(p).st_dev, os.stat(p).st_ino) for p in paths}
    for d, _, files in os.walk(os.path.join(cache_dir(), "artifacts")):
        for f in files:
            path = os.path.join(d, f)
            st = os.stat(path)
            if (st.st_dev, st.st_ino) in inodes:
                os.remove(path)
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
    if not jobs:
        sys.exit(run(["lake", "exe", "fren_coverage", "--static", "--new", a.base]))
    runtime, gcov = toolchain()
    # `-Kcoverage_dir` puts the worktree's directory in the key of each
    # object in the artifact cache, since the object writes its counters
    # there (`lakefile.lean`).
    k = [f"-Kcoverage={runtime}", f"-Kcoverage_dir={ROOT}"]
    build = heavy(["lake", "-R", *k, "build", "fren_test", "fren_coverage"])
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
