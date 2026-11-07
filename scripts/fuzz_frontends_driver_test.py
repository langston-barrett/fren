#!/usr/bin/env python3
"""Exercise the real fuzzer CLI, supervisors and workers, including recovery.

Run as `fren_test --job frontendFuzzDriver`, or after building
fren_fuzz_frontends: lake env python3 -I scripts/fuzz_frontends_driver_test.py.
The caller supplies heavy/offline isolation; no builds or downloads run here.
"""

from contextlib import contextmanager
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake/build/bin/fren_fuzz_frontends"
SEED = 992000


class DriverTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="fuzz-driver-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    @contextmanager
    def process(self, name, args):
        directory = self.root / name
        directory.mkdir()
        with (directory / "run.log").open("w") as log:
            proc = subprocess.Popen([str(EXE), *args, "--out", str(directory)],
                                    cwd=ROOT, stdout=log, stderr=log)
            try:
                yield proc, directory
            finally:
                # Keep heavy's process group intact. Stop only this parent
                # and workers with its exact run IDs, including a stopped
                # peer left behind by a failed assertion or an early return.
                if proc.poll() is None:
                    proc.kill()
                proc.wait(timeout=10)
                for pid in self.workers(proc, include_orphans=True).values():
                    try:
                        os.kill(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass

    def wait(self, proc, directory, code):
        self.assertEqual(proc.wait(timeout=120), code,
                         (directory / "run.log").read_text())

    def rows(self, directory, count, files):
        paths = sorted(directory.glob("results-*.jsonl"))
        self.assertEqual(len(paths), files)
        lanes = [[json.loads(line) for line in path.read_text().splitlines()]
                 for path in paths]
        rows = sorted((row for lane in lanes for row in lane), key=lambda r: r["seed"])
        self.assertEqual([r["seed"] for r in rows], list(range(SEED, SEED + count)))
        self.assertFalse(list(directory.glob("current-*")), "work files leaked")
        if files == 2:
            # Inspect each append-only file, not just their union: this
            # catches overlapping lanes and lost work in the odd remainder.
            self.assertTrue(paths[0].name.endswith("-p0.jsonl"))
            self.assertTrue(paths[1].name.endswith("-p1.jsonl"))
            for lane, start, size in zip(lanes, (SEED, SEED + count // 2),
                                         (count // 2, count - count // 2)):
                self.assertEqual([r["seed"] for r in lane], list(range(start, start + size)))
        return rows

    def report(self, directory, count, crashes=0, timeouts=0):
        out = subprocess.run([str(EXE), "--report", str(directory)], cwd=ROOT,
                             text=True, capture_output=True, timeout=30)
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertTrue(out.stdout.startswith(f"{count} specs:"), out.stdout)
        self.assertIn(f"{crashes} crashed and {timeouts} took too long", out.stdout)
        return out.stdout

    def args(self, count, jobs=()):
        return ["--avoid-known", "--guards", "--count", str(count),
                "--seed", str(SEED), "--spec-timeout", "90", *jobs]

    def test_empty_single_and_odd_ranges(self):
        for count in (0, 1, 5):
            outcomes = []
            for label, jobs in (("default", ()), ("serial", ("--jobs", "1")),
                                ("parallel", ("--jobs", "2"))):
                with self.subTest(count=count, jobs=label):
                    with self.process(f"{label}-{count}", self.args(count, jobs)) as (proc, directory):
                        self.wait(proc, directory, 0)
                        rows = self.rows(directory, count, 2 if label == "parallel" and count > 1 else 1)
                        self.assertTrue(all(r["status"] in ("ok", "known", "inconclusive") for r in rows))
                        self.report(directory, count)
                        outcomes.append([{k: v for k, v in r.items()
                                          if k not in ("ms", "solverTimeoutMs")} for r in rows])
            self.assertEqual(len(outcomes), 3)
            self.assertEqual(outcomes[0], outcomes[1])
            self.assertEqual(outcomes[0], outcomes[2])

    def test_invalid_jobs(self):
        for i, jobs in enumerate((("0",), ("3",), ("-1",), ("invalid",), ())):
            with self.subTest(jobs=jobs):
                with self.process(str(i), ["--count", "0", "--jobs", *jobs]) as (proc, directory):
                    self.wait(proc, directory, 2)
                    self.assertIn("usage: fren_fuzz_frontends", (directory / "run.log").read_text())
                    self.assertFalse(list(directory.glob("results-*")))

    def workers(self, parent, include_orphans=False):
        # ps works on Linux and macOS. Require the exact parent and worker
        # arguments; never signal another test's or another author's worker.
        out = subprocess.run(["ps", "-axo", "pid=,ppid=,args="], text=True,
                             capture_output=True, check=True, timeout=10)
        workers = {}
        for line in out.stdout.splitlines():
            fields = line.split()
            if len(fields) < 5 or fields[2:4] != [str(EXE), "--worker"]:
                continue
            own_id = fields[4] in (str(parent.pid), f"{parent.pid}-p0", f"{parent.pid}-p1")
            if own_id and (fields[1] == str(parent.pid) or include_orphans):
                workers[fields[4]] = int(fields[0])
        return workers

    def until(self, proc, directory, action):
        deadline = time.monotonic() + 90
        while time.monotonic() < deadline:
            self.assertIsNone(proc.poll(), (directory / "run.log").read_text())
            result = action()
            if result is not None:
                return result
            time.sleep(0.01)
        self.fail("worker synchronization timed out:\n" + (directory / "run.log").read_text())

    def test_crash_recovers_and_waits_for_peer(self):
        with self.process("crash", self.args(6, ("--jobs", "2"))) as (proc, directory):
            ids = [f"{proc.pid}-p{i}" for i in range(2)]
            stopped = {}

            def stop_workers():
                for run_id, pid in self.workers(proc).items():
                    if run_id in ids and run_id not in stopped:
                        os.kill(pid, signal.SIGSTOP)
                        stopped[run_id] = pid
                return stopped if len(stopped) == 2 else None

            self.until(proc, directory, stop_workers)
            # Hold the peer before it finishes. Let lane 0 reach its first
            # active spec, then stop it to read a stable progress record.
            victim = stopped[ids[0]]
            os.kill(victim, signal.SIGCONT)

            def stop_active():
                progress = directory / f"current-{ids[0]}.seed"
                if not progress.read_text().strip():
                    return None
                os.kill(victim, signal.SIGSTOP)
                text = progress.read_text().strip()
                if text:
                    return int(text.splitlines()[0])
                os.kill(victim, signal.SIGCONT)
                return None

            failed = self.until(proc, directory, stop_active)
            self.assertEqual(failed, SEED, "injection missed the first spec")
            os.kill(victim, signal.SIGKILL)

            def recovered():
                path = directory / f"results-{ids[0]}.jsonl"
                # A final partial append is possible while the worker runs.
                text = path.read_text()
                if not text.endswith("\n"):
                    return None
                rows = [json.loads(line) for line in text.splitlines()]
                if ([r["seed"] for r in rows] == list(range(SEED, SEED + 3))
                        and not (directory / f"current-{ids[0]}.seed").exists()):
                    return rows
                return None

            recovered_rows = self.until(proc, directory, recovered)
            self.assertEqual([r["status"] for r in recovered_rows].count("crash"), 1)
            # The failed lane has recovered and exhausted its range. The
            # parent must still wait for the deliberately stopped peer.
            peer_rows = (directory / f"results-{ids[1]}.jsonl").read_text().splitlines()
            self.assertLess(len(peer_rows), 3, "peer finished before it was stopped")
            with self.assertRaises(subprocess.TimeoutExpired):
                proc.wait(timeout=0.5)
            os.kill(stopped[ids[1]], signal.SIGCONT)
            self.wait(proc, directory, 1)
            rows = self.rows(directory, 6, 2)
            self.assertEqual([r["seed"] for r in rows if r["status"] == "crash"], [failed])
            self.assertTrue(all(r["status"] in ("ok", "known", "inconclusive")
                                for r in rows if r["seed"] != failed))
            report = self.report(directory, 6, crashes=1)
            self.assertIn(f"| {failed} |", report)
            self.assertTrue((directory / f"crash-seed{failed}.fren").is_file())

    def test_timeouts_are_recorded_in_both_lanes(self):
        args = ["--avoid-known", "--jobs", "2", "--count", "2", "--seed", str(SEED),
                "--spec-timeout", "0"]
        with self.process("timeout", args) as (proc, directory):
            self.wait(proc, directory, 1)
            rows = self.rows(directory, 2, 2)
            self.assertEqual([r["status"] for r in rows], ["timeout", "timeout"])
            self.report(directory, 2, timeouts=2)
            for row in rows:
                self.assertTrue((directory / f"timeout-seed{row['seed']}.fren").is_file())


if __name__ == "__main__":
    unittest.main()
