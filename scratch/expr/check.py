#!/usr/bin/env python3
"""Reproduce the scratch experiment with the already-built Lake environment.

Run through scripts/heavy --offline. No package build, cache restore or download
is requested. This compiles only the two prototype imports, then elaborates and
executes its tests. Negative fixtures must fail for their specific reason.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import time


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(name, args, out, expected_error=None):
    log = out / (name + ".log")
    start = time.monotonic()
    pid = os.fork()
    if pid == 0:
        with log.open("wb") as stream:
            os.dup2(stream.fileno(), 1)
            os.dup2(stream.fileno(), 2)
            os.execvp(args[0], args)
    _, status, usage = os.wait4(pid, 0)
    seconds = time.monotonic() - start
    code = os.waitstatus_to_exitcode(status)
    output = log.read_text()
    ok = code == 0 if expected_error is None else code == 1 and expected_error in output
    if name == "tests":
        ok = ok and "expression prototype: passed;" in output
    if name == "axioms":
        ok = ok and "sorryAx" not in output and "Classical.choice" not in output
        ok = ok and "WellFounded.Nat.fix" in output
    result = {
        "name": name, "argv": args, "exit": code, "expected_error": expected_error,
        "passed": ok, "execution_seconds": seconds,
        "user_seconds": usage.ru_utime, "system_seconds": usage.ru_stime,
        "max_rss_bytes": usage.ru_maxrss * (1 if sys.platform == "darwin" else 1024),
        "log_sha256": sha256(log),
    }
    print(json.dumps(result), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if not Path("scratch/expr/Prototype.lean").exists():
        parser.error("run from the repository root")
    args.out.mkdir(parents=True, exist_ok=False)
    lean = ["lake", "--no-cache", "env", "lean", "-DwarningAsError=true"]
    artifacts = Path(".lake/build/lib/lean/scratch/expr")
    artifacts.mkdir(parents=True, exist_ok=True)
    steps = [
        ("indexed-layer", ["scratch/expr/attempts/IndexedLayer.lean"], "nested inductive datatypes parameters cannot contain local variables"),
        ("indexed-direct", ["scratch/expr/attempts/IndexedDirect.lean"], "nested inductive datatypes parameters cannot contain local variables"),
        ("opaque-traversal", ["scratch/expr/attempts/OpaqueTraversal.lean"], "fail to show termination"),
        ("core", ["-o", str(artifacts / "Prototype.olean"), "scratch/expr/Prototype.lean"], None),
        ("core-repeat", ["-o", str(artifacts / "Prototype.olean"), "scratch/expr/Prototype.lean"], None),
        ("codec", ["-o", str(artifacts / "Codec.olean"), "scratch/expr/Codec.lean"], None),
        ("forbidden-gate", ["scratch/expr/attempts/ForbiddenGate.lean"], "HasSugar Phase.low"),
        ("axioms", ["scratch/expr/Audit.lean"], None),
        ("tests", ["--run", "scratch/expr/Tests.lean"], None),
    ]
    results = []
    for name, tail, expected in steps:
        results.append(run(name, lean + tail, args.out, expected))
        if not results[-1]["passed"]:
            break
    manifest = {
        "scope": "warm pinned dependencies; source elaboration, not a cold toolchain build",
        "timing": "each child including Lake env and Lean, excluding outer Heavy/fd admission",
        "memory": "wait4 child high-water RSS; not process-tree simultaneous RSS",
        "sources": {str(p): sha256(p) for p in sorted(Path("scratch/expr").rglob("*")) if p.is_file()},
        "artifacts": {str(p): sha256(p) for p in sorted(artifacts.glob("*")) if p.is_file()},
        "results": results,
    }
    (args.out / "results.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return 0 if len(results) == len(steps) and all(r["passed"] for r in results) else 1


if __name__ == "__main__":
    sys.exit(main())
