#!/usr/bin/env python3
"""Real deadline and waitable-anchor regressions. No workload benchmark.
Old-source lifecycle probes suppress every numeric group signal in a test
interposer before the kernel; they never force PID reuse or signal outsiders.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent


def wait_for(predicate, label):
    until = time.monotonic() + 3
    while not predicate():
        assert time.monotonic() < until, label
        time.sleep(.002)


def producer(case, work, shim, fault):
    session = Path(os.environ["HEAVY_BUDGET_DIR"])
    env = dict(os.environ)
    registry = lease = None
    proc = None
    stopped = False
    try:
        if case in ("initial-lock", "timely-lock", "reacquire"):
            registry = (session / "registry").open("r+")
            if case in ("initial-lock", "timely-lock"): fcntl.flock(registry, fcntl.LOCK_EX)
            else:
                lease = (session / "ticket-00000000000000000099").open("w+")
                os.chmod(lease.name, 0o600); fcntl.flock(lease, fcntl.LOCK_EX)
                start = Path("/proc/self/stat").read_text().rsplit(")", 1)[1].split()[19]
                ns = Path("/proc/self/ns/pid").stat()
                boot = Path("/proc/sys/kernel/random/boot_id").read_text().strip()
                lease.write(f"99 1 7 {os.getpid()} {start} {boot}:{ns.st_dev}:{ns.st_ino}\n"); lease.flush()
        else:
            env.update(LD_PRELOAD=str(fault), BOUNDARY_TARGET=str(session / "ticket-00000000000000000001"),
                       BOUNDARY_READY=str(work / "paused"), BOUNDARY_RESUME=str(work / "resume"),
                       BOUNDARY_LOG=str(work / "io.jsonl"))
            env["BOUNDARY_SNAPSHOT" if case == "snapshot" else "BOUNDARY_GRANT"] = "1"
        proc = subprocess.Popen([str(shim), str(work / "Input.lean")], env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if case in ("initial-lock", "timely-lock"):
            def opened():
                assert proc.poll() is None, "observer exited before lock synchronization"
                for fd in Path(f"/proc/{proc.pid}/fd").iterdir():
                    try:
                        if os.readlink(fd) == str(session / "registry"): return True
                    except FileNotFoundError: pass
                return False
            wait_for(opened, "registry not opened")
        elif case == "reacquire":
            wait_for(lambda: (session / "ticket-00000000000000000001").exists(), "no stable waiting ticket")
            fcntl.flock(registry, fcntl.LOCK_EX)
        else:
            wait_for(lambda: (work / "paused").exists(), "snapshot/publication pause not reached")
        if registry:
            proc.send_signal(signal.SIGSTOP)
            wait_for(lambda: Path(f"/proc/{proc.pid}/stat").read_text().rsplit(")", 1)[1].split()[0] == "T", "not stopped")
            stopped = True
        start = time.monotonic_ns(); time.sleep(.02 if case == "timely-lock" else .4); end = time.monotonic_ns()
        if lease: lease.close(); lease = None
        if registry:
            fcntl.flock(registry, fcntl.LOCK_UN)
            proc.send_signal(signal.SIGCONT); stopped = False
        else: (work / "resume").touch()
        stdout, stderr = proc.communicate(timeout=3)
        (work / "producer.json").write_text(json.dumps(dict(status=proc.returncode, pause_ns=end-start,
            configured_wait_ms=250, stdout=stdout.decode(), stderr=stderr.decode()), indent=2))
    finally:
        if stopped: proc.send_signal(signal.SIGCONT)
        if proc and proc.poll() is None: proc.kill()
        if proc: proc.communicate(timeout=3)
        if registry: registry.close()
        if lease: lease.close()


def main():
    if sys.argv[1:2] == ["--producer"]:
        producer(sys.argv[2], *map(Path, sys.argv[3:])); return
    wall_start = time.monotonic()
    wall = subprocess.run([sys.executable, "-I", str(HERE / "wall_test.py")], capture_output=True, timeout=20)
    wall_seconds = time.monotonic() - wall_start
    assert wall.returncode == 0, (wall.stdout, wall.stderr)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bin", type=Path, default=HERE / ".lake/build/bin")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--expect-old", action="store_true")
    args = parser.parse_args()
    if args.output:
        work = args.output.absolute(); work.mkdir(parents=True, exist_ok=False)
    else:
        (HERE / "test-work").mkdir(exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix="boundaries-", dir=HERE / "test-work"))
    binary = args.bin.absolute()
    fault = work / "boundaries.so"
    cc = ["cc", "-shared", "-fPIC", "-O2", "-Wall", "-Wextra", "-Werror",
          str(HERE / "budget_boundaries.c"), "-ldl", "-o", str(fault)]
    compiled = subprocess.run(cc, capture_output=True, timeout=10)
    (work / "cc.log").write_bytes(compiled.stdout + compiled.stderr)
    assert compiled.returncode == 0, compiled.stderr
    report = dict(expected="old bugs" if args.expect_old else "fixed behavior", cases=[], compiler_command=cc,
        wall=dict(status=wall.returncode, seconds=wall_seconds, stdout=wall.stdout.decode(), stderr=wall.stderr.decode()),
        binaries={p:hashlib.sha256((binary / p).read_bytes()).hexdigest() for p in ("heavy_observe", "budget_session")})
    cases = ["initial-lock", "reacquire", "snapshot", "grant-write", "timely-lock", "ignored-chld", "auto-reap", "custom-chld",
             "lost-anchor", "query-error", "last-query-error", "normal-true", "normal-exit"]
    for case in cases:
        begin = time.monotonic(); directory = work / case; directory.mkdir()
        manifest = directory / "manifest"; manifest.write_text("")
        env = dict(os.environ); preexec = None
        if case in cases[:5]:
            overlay = directory / "overlay"; (overlay / "bin").mkdir(parents=True); (overlay / "records").mkdir()
            (overlay / "bin/lean").write_bytes((binary / "heavy_observe").read_bytes()); (overlay / "bin/lean").chmod(0o700)
            fixture = directory / "compiler"
            fixture.write_text('#!/usr/bin/python3\nimport sys\nfrom pathlib import Path\n'
                'if sys.argv[1:] in (["--version"],["--githash"]): print("owned boundary fixture")\n'
                f'else: Path({str(directory / "compiler-started")!r}).touch()\n')
            fixture.chmod(0o700); (overlay / "real-lean.path").write_text(str(fixture))
            (directory / "Input.lean").write_text("owned boundary fixture")
            command = [str(binary / "budget_session"), str(directory / "session"), "10", "1", "7", "250", str(manifest),
                "--", "/usr/bin/python3", "-I", str(Path(__file__).resolve()), "--producer", case, str(directory),
                str(overlay / "bin/lean"), str(fault)]
        else:
            env.update(LD_PRELOAD=str(fault), BOUNDARY_GROUP_GUARD="1", BOUNDARY_LOG=str(directory / "io.jsonl"))
            if case == "ignored-chld":
                env["BOUNDARY_CHLD"] = "inherited"
                preexec = lambda: signal.signal(signal.SIGCHLD, signal.SIG_IGN)
            if case == "auto-reap": env["BOUNDARY_CHLD"] = "auto"
            if case == "custom-chld": env["BOUNDARY_CHLD"] = "custom"
            if case == "lost-anchor": env["BOUNDARY_REAP"] = "1"
            if case == "query-error": env["BOUNDARY_QUERY_ERROR"] = "1"
            if case == "last-query-error": env["BOUNDARY_LAST_QUERY_ERROR"] = "1"
            command = [str(binary / "budget_session"), str(directory / "session"), "10", "1", "9", "2500", str(manifest),
                       "--", "/bin/sh", "-c", "exit 7"] if case == "normal-exit" else [
                       str(binary / "budget_session"), str(directory / "session"), "10", "1", "9", "2500", str(manifest),
                       "--", "/bin/true"]
        child = subprocess.Popen(command, env=env, preexec_fn=preexec, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try: stdout, stderr = child.communicate(timeout=9)
        except BaseException:
            child.send_signal(signal.SIGTERM)
            try: child.communicate(timeout=3)
            except subprocess.TimeoutExpired: child.kill(); child.communicate(timeout=2)
            raise
        (directory / "stdout").write_bytes(stdout); (directory / "stderr").write_bytes(stderr)
        row = dict(case=case, command=command, status=child.returncode, seconds=time.monotonic()-begin,
                   stdout=stdout.decode(), stderr=stderr.decode())
        if case in cases[:5]:
            rows = [json.loads(p.read_text()) for p in (overlay / "records").glob('process-*.json')]
            assert child.returncode == 0 and len(rows) == 1, row
            raw = rows[0]; started = (directory / "compiler-started").exists()
            row.update(records=rows, producer=json.loads((directory / "producer.json").read_text()), started=started)
            if case == "timely-lock": assert started and raw["gate_errno"] == 0 and raw["admission_wait_ns"] < 250000000, row
            elif args.expect_old: assert started and raw["gate_errno"] == 0 and raw["admission_wait_ns"] > 250000000, row
            else: assert not started and raw["gate_errno"] == 110 and not raw["child_present"] and raw["wrapper_code"] == 125, row
        else:
            events = [json.loads(s) for s in (directory / "io.jsonl").read_text().splitlines()]
            parent_events = [r for r in events if r["pid"] == child.pid]
            attempts = [r for r in parent_events if r["event"] == "group-attempt"]
            unsafe = [r for r in attempts if r["c"] != 0]
            forks = [r for r in parent_events if r["event"] == "fork"]
            row.update(events=events, unsafe_attempts=len(unsafe), group_attempts=len(attempts), forks=len(forks), delivered_group_signals=0)
            if case in ("ignored-chld", "auto-reap", "custom-chld", "query-error"):
                if args.expect_old:
                    assert len(forks) == 1
                    if case in ("ignored-chld", "auto-reap"): assert unsafe and child.returncode == 125, row
                else: assert child.returncode == 125 and not forks and not attempts, row
            elif case == "lost-anchor":
                assert child.returncode == 125 and any(r['event']=='reaped' and r['a']>0 for r in parent_events), row
                assert bool(unsafe) == args.expect_old and (args.expect_old or not attempts), row
            elif case == "last-query-error":
                if args.expect_old: assert child.returncode == 0 and len(attempts) == 2, row
                else: assert child.returncode == 125 and len(attempts) == 1 and not unsafe, row
            else:
                assert child.returncode == (7 if case == "normal-exit" else 0) and len(forks) == 1 and not unsafe, row
        report['cases'].append(row); (work / "report.json").write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(report=str(work / "report.json"), expected=report['expected'], cases=cases)))


if __name__ == "__main__": main()
