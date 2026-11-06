#!/usr/bin/env python3
"""The verdict of the `pre-approval` workflow, its last job of the same name
(`Reqs/dev/Testing#continuous-integration`).

    python3 scripts/pre_approval_verdict.py
    python3 scripts/pre_approval_verdict.py test

It reads the results of the workflow's jobs from the environment: `BUILD`,
`TEST` and `BOOK`, each `success`, `failure`, `cancelled` or `skipped`;
`BUILT`, the `book` job's output, `true` if it built the book; and `EVENT`,
the event that the run is of. It exits 0 if the build and every shard
passed and, unless the run is in the merge queue (`merge_group`), where
the book is not built, the book was built and passed; and 1 otherwise,
saying why. Any other event, or none, needs the book.

`test` checks the verdict on every combination of the jobs' results, by
running this script as the workflow does.
"""

import itertools
import os
import subprocess
import sys

RESULTS = ["success", "failure", "cancelled", "skipped"]


def reasons(env):
    """Why the run fails, or nothing if it passes."""
    out = []
    for job in ["BUILD", "TEST"]:
        if env.get(job) != "success":
            out.append(f"{job.lower()}: {env.get(job)}")
    if env.get("EVENT") != "merge_group":
        if env.get("BOOK") != "success":
            out.append(f"book: {env.get('BOOK')}")
        elif env.get("BUILT") != "true":
            out.append("book: passed without building the book, since no test driver was downloaded")
    return out


def main():
    why = reasons(os.environ)
    for r in why:
        print(f"pre-approval fails: {r}")
    sys.exit(1 if why else 0)


def run(env):
    """The exit code of this script, run as the workflow runs it."""
    full = {k: v for k, v in os.environ.items() if k not in ("BUILD", "TEST", "BOOK", "BUILT", "EVENT")}
    full.update(env)
    return subprocess.run([sys.executable, "-I", "-B", __file__], env=full, capture_output=True).returncode


def test():
    failures = []

    def expect(env, code):
        got = run(env)
        if got != code:
            failures.append(f"{env}: exit {got}, expected {code}")

    # Every combination: it passes exactly where the build and the tests
    # passed and, but in the merge queue, the book passed and was built. An
    # event of `None` is unset; any event but `merge_group` needs the book.
    for event, build, tests, book, built in itertools.product(
        ["pull_request", "merge_group", "push", "workflow_dispatch", "PULL_REQUEST", "", None],
        RESULTS, RESULTS, RESULTS, ["true", "false", ""],
    ):
        green = build == "success" and tests == "success"
        if event != "merge_group":
            green = green and book == "success" and built == "true"
        env = {"BUILD": build, "TEST": tests, "BOOK": book, "BUILT": built}
        if event is not None:
            env["EVENT"] = event
        expect(env, 0 if green else 1)
    # The cases of the review of #688, written out: a failed build fails,
    # whatever the book did.
    expect({"EVENT": "pull_request", "BUILD": "failure", "TEST": "success", "BOOK": "success", "BUILT": "true"}, 1)
    expect({"EVENT": "merge_group", "BUILD": "failure", "TEST": "success", "BOOK": "skipped", "BUILT": ""}, 1)
    expect({"EVENT": "pull_request", "BUILD": "success", "TEST": "success", "BOOK": "success", "BUILT": "false"}, 1)
    expect({"EVENT": "merge_group", "BUILD": "success", "TEST": "success", "BOOK": "skipped", "BUILT": ""}, 0)
    # An unset result is no success, and an unset event needs the book.
    expect({"EVENT": "pull_request"}, 1)
    expect({"BUILD": "success", "TEST": "success"}, 1)
    for f in failures:
        print(f, file=sys.stderr)
    if failures:
        sys.exit(1)
    print("pre_approval_verdict: all passed")


if __name__ == "__main__":
    if sys.argv[1:] == ["test"]:
        test()
    elif sys.argv[1:]:
        sys.exit(__doc__)
    else:
        main()
