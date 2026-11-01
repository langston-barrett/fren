#!/usr/bin/env python3
"""Measure each module's peak resident memory and wall time in a Lake build.

    python3 scripts/measure_build.py run [--log FILE] -- heavy lake build --wfail
    python3 scripts/measure_build.py report FILE [--top N]

`run` runs the command with Lake pointed at a copy of the toolchain's
sysroot whose `lean` and `clang` are wrappers. Each wrapper runs the real
tool, waits for it with `wait4`, and appends a line of JSON to the log
(default `build-times.jsonl`): the step (a module's elaboration, its C
compilation `Module:c.o`, or a link), its wall time, its CPU time, its
peak resident memory and when it started. Then it prints the report.
`report` prints the report of a log: the slowest steps, those with the
most memory, a summary by kind of module, and the peak of the memory of
the steps that ran at once.

For a clean build, delete `.lake/build` first (not `.lake/packages`).
Lake may rebuild some of the dependencies too; their steps are in the
log, named `package/Module`.

Lake runs steps in parallel, so a step's wall time includes waiting for
cores. A step's CPU time includes that of the processes it waited for,
and its peak memory (`ru_maxrss`) is that of the largest of them. The
peak of the steps that ran at once is the largest sum over steps whose
runs overlap, an upper bound, since each step's peak need not be at the
same moment.
Works on macOS and Linux. Run it through `heavy`, as any build.
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.abspath(__file__)
WRAPPED = ("lean", "clang")


def maxrss_bytes(ru):
    # macOS reports bytes, Linux kilobytes.
    return ru.ru_maxrss if sys.platform == "darwin" else ru.ru_maxrss * 1024


def step_name(tool, args):
    """The step that a `lean` or `clang` invocation is: `Module`,
    `Module:c.o`, or `link:<output>`; None for other invocations
    (`lean --githash`, say), which aren't logged."""
    out = None
    for i, a in enumerate(args[:-1]):
        if a == "-o":
            out = args[i + 1]
    if tool == "lean":
        if not any(a.endswith(".lean") for a in args) or out is None:
            return None
        path = out
    else:
        if out is None:
            return None
        if "-c" not in args:
            return "link:" + os.path.basename(out)
        path = out
    marker = "/lib/lean/" if tool == "lean" else "/ir/"
    if marker in path:
        rel = path.split(marker, 1)[1]
    else:
        rel = os.path.basename(path)
    module = rel.split(".", 1)[0].replace("/", ".")
    pkg = ""
    if "/.lake/packages/" in path:
        pkg = path.split("/.lake/packages/", 1)[1].split("/", 1)[0] + "/"
    return pkg + module + ("" if tool == "lean" else ":c.o")


def wrap(log, tool, real, args):
    name = step_name(tool, args)
    if name is None:
        os.execv(real, [real] + args)
    start = time.time()
    t0 = time.monotonic()
    proc = subprocess.Popen([real] + args)
    while True:
        try:
            _, status, ru = os.wait4(proc.pid, 0)
            break
        except InterruptedError:
            continue
    wall = time.monotonic() - t0
    entry = {
        "step": name,
        "tool": tool,
        "start": start,
        "wall": round(wall, 3),
        "cpu": round(ru.ru_utime + ru.ru_stime, 3),
        "rss": maxrss_bytes(ru),
        "status": os.waitstatus_to_exitcode(status),
    }
    with open(log, "a") as f:
        f.write(json.dumps(entry) + "\n")
    code = os.waitstatus_to_exitcode(status)
    sys.exit(code if code >= 0 else 128 - code)


def fake_sysroot(dest, log):
    """A directory like the toolchain's sysroot, with `lean` and `clang`
    replaced by wrappers that log to `log`."""
    real = subprocess.run(
        ["lean", "--print-prefix"], capture_output=True, text=True, check=True
    ).stdout.strip()
    for entry in os.listdir(real):
        if entry != "bin":
            os.symlink(os.path.join(real, entry), os.path.join(dest, entry))
    os.mkdir(os.path.join(dest, "bin"))
    for exe in os.listdir(os.path.join(real, "bin")):
        src = os.path.join(real, "bin", exe)
        dst = os.path.join(dest, "bin", exe)
        if exe in WRAPPED:
            with open(dst, "w") as f:
                f.write(
                    f'#!/bin/sh\nexec {sys.executable} {HERE} wrap {log} {exe} {src} "$@"\n'
                )
            os.chmod(dst, 0o755)
        else:
            os.symlink(src, dst)


def gib(n):
    return f"{n / 2**30:.2f}"


def kind(step):
    name = step.split(":", 1)[0]
    if "/" in name:
        return "dependencies"
    if step.startswith("link:"):
        return "links"
    suffix = " (C)" if step.endswith(":c.o") else ""
    for prefix in ("Reqs", "Impls", "FrenCli", "FrenCore", "FrenTest", "Fren"):
        if name == prefix or name.startswith(prefix + "."):
            return prefix + suffix
    return "other" + suffix


def report(path, top):
    entries = (
        [json.loads(line) for line in open(path) if line.strip()]
        if os.path.exists(path)
        else []
    )
    if not entries:
        print("no steps logged")
        return
    first = min(e["start"] for e in entries)
    last = max(e["start"] + e["wall"] for e in entries)
    print(
        f"{len(entries)} steps, {last - first:.0f} s from the first step's start to the last one's end, "
        f"{sum(e['cpu'] for e in entries):.0f} s CPU.\n"
    )

    def table(title, key, rows):
        print(f"**{title}**\n")
        print("| step | peak memory (GiB) | wall (s) | CPU (s) |")
        print("|---|---:|---:|---:|")
        for e in sorted(rows, key=key, reverse=True)[:top]:
            print(
                f"| {e['step']} | {gib(e['rss'])} | {e['wall']:.1f} | {e['cpu']:.1f} |"
            )
        print()

    table(f"Top {top} by peak memory", lambda e: e["rss"], entries)
    table(f"Top {top} by wall time", lambda e: e["wall"], entries)

    groups = {}
    for e in entries:
        groups.setdefault(kind(e["step"]), []).append(e)
    print("**By kind of step**\n")
    print("| kind | steps | wall (s) | CPU (s) | largest peak memory (GiB) |")
    print("|---|---:|---:|---:|---:|")
    for k, es in sorted(groups.items(), key=lambda kv: -sum(e["cpu"] for e in kv[1])):
        print(
            f"| {k} | {len(es)} | {sum(e['wall'] for e in es):.0f} | {sum(e['cpu'] for e in es):.0f} | "
            f"{gib(max(e['rss'] for e in es))} |"
        )
    print()

    events = sorted(
        [(e["start"], 1, e) for e in entries]
        + [(e["start"] + e["wall"], 0, e) for e in entries],
        key=lambda t: (t[0], t[1]),
    )
    running, total, peak, peak_at = {}, 0, 0, []
    for _, starts, e in events:
        if starts:
            running[id(e)] = e
            total += e["rss"]
            if total > peak:
                peak, peak_at = total, sorted(running.values(), key=lambda x: -x["rss"])
        else:
            running.pop(id(e))
            total -= e["rss"]
    names = ", ".join(f"{x['step']} ({gib(x['rss'])})" for x in peak_at[:6])
    print(
        f"Peak of the memory of the steps that ran at once (an upper bound): {gib(peak)} GiB, "
        f"{len(peak_at)} steps: {names}{', ...' if len(peak_at) > 6 else ''}."
    )


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "wrap":
        log, tool, real = sys.argv[2:5]
        wrap(log, tool, real, sys.argv[5:])
    p = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    sub = p.add_subparsers(dest="mode", required=True)
    r = sub.add_parser("run", help="run a build with the wrappers, then report")
    r.add_argument("--log", default="build-times.jsonl")
    r.add_argument("--top", type=int, default=20)
    r.add_argument("command", nargs=argparse.REMAINDER)
    q = sub.add_parser("report", help="report on a log")
    q.add_argument("log")
    q.add_argument("--top", type=int, default=20)
    a = p.parse_args()
    if a.mode == "report":
        report(a.log, a.top)
        return
    command = a.command[1:] if a.command[:1] == ["--"] else a.command
    if not command:
        p.error("run needs a command, e.g. -- heavy lake build --wfail")
    log = os.path.abspath(a.log)
    with tempfile.TemporaryDirectory(prefix="fren-sysroot-") as root:
        fake_sysroot(root, log)
        env = dict(os.environ, LEAN_SYSROOT=root, LAKE_OVERRIDE_LEAN="true")
        code = subprocess.run(command, env=env).returncode
    report(log, a.top)
    sys.exit(code)


if __name__ == "__main__":
    main()
