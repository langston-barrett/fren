"""Bounded test subprocesses; adopt and reap only this harness's children."""
import ctypes
import errno
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


def initialize():
    if sys.platform == "linux":
        # Orphaned debugger inferiors remain this test's children, so a
        # timeout cannot leave them to the CI runner's eventual cleanup.
        if ctypes.CDLL(None, use_errno=True).prctl(36, 1, 0, 0, 0) != 0:
            raise OSError(ctypes.get_errno(), "cannot adopt native test descendants")


def children(pid):
    try:
        return [int(p) for p in Path(f"/proc/{pid}/task/{pid}/children").read_text().split()]
    except FileNotFoundError:
        return []


def identity(pid):
    try:
        fields = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()
        return int(fields[1]), fields[19]  # parent PID and start time
    except FileNotFoundError:
        return None


def cleanup(process, peers):
    killed = set()
    reaped = set()
    errors = []
    deadline = time.monotonic() + 2
    while True:
        pending = [os.getpid()]
        owned = {}
        for parent in pending:
            for pid in children(parent):
                observed = identity(pid)
                if pid not in peers and observed and observed[0] == parent and pid not in owned:
                    owned[pid] = observed[1]
                    pending.append(pid)
        if process.poll() is None:
            observed = identity(process.pid)
            owned[process.pid] = observed[1] if observed else None
        for pid, started in owned.items():
            try:
                # A pidfd pins this observed child's identity across exit
                # and PID reuse; never signal an unrelated replacement.
                if hasattr(os, "pidfd_open"):
                    fd = os.pidfd_open(pid)
                    try:
                        observed = identity(pid)
                        if observed is None or observed[1] != started:
                            continue
                        signal.pidfd_send_signal(fd, signal.SIGKILL)
                    finally:
                        os.close(fd)
                else:
                    os.kill(pid, signal.SIGKILL)
                killed.add(pid)
            except OSError as error:
                # A just-reaped leader can lose its thread-group identity
                # before pidfd_open, which Linux may report as EINVAL.
                if error.errno != errno.ESRCH and not (error.errno == errno.EINVAL and identity(pid) is None):
                    errors.append(f"signal child {pid}: {error}")
        for pid in children(os.getpid()):
            if pid in peers or pid == process.pid:
                continue
            try:
                if os.waitpid(pid, os.WNOHANG)[0]:
                    reaped.add(pid)
            except ChildProcessError:
                pass
        remaining = [p for p in children(os.getpid()) if p not in peers]
        if process.poll() is None and process.pid not in remaining:
            remaining.append(process.pid)
        if not remaining or time.monotonic() >= deadline:
            break
        time.sleep(0.01)
    return {"killed": sorted(killed), "reaped": sorted(reaped),
            "remaining": remaining, "errors": errors, "child_returncode": process.returncode}


class NativeTimeout(AssertionError):
    def __init__(self, receipt):
        self.receipt = receipt
        super().__init__(json.dumps(receipt))


def run(command, *, timeout=60, peers=(), **kwargs):
    start = time.monotonic()
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               text=True, start_new_session=True, **kwargs)
    try:
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired as error:
            receipt = cleanup(process, peers)
            receipt.update(timed_out=True, timeout=timeout, command=command,
                           seconds=time.monotonic() - start,
                           stdout=error.stdout.decode(errors="replace") if isinstance(error.stdout, bytes) else error.stdout,
                           stderr=error.stderr.decode(errors="replace") if isinstance(error.stderr, bytes) else error.stderr)
            # Do not retry an unbounded communicate after killing only the
            # leader: a descendant can still hold either output pipe open.
            raise NativeTimeout(receipt) from error
        result = subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
        # A fatal native child can leave its signal-sending helper behind.
        # Reap such adoptions after normal completion too, not just timeout.
        result.cleanup = cleanup(process, peers)
        if result.cleanup["remaining"] or result.cleanup["errors"]:
            raise AssertionError(f"native test cleanup failed: {result.cleanup}")
        return result
    finally:
        # Popen's context manager waits without a bound on exit. Avoid it
        # here so even a failed cleanup remains an explicit bounded failure.
        process.stdout.close()
        process.stderr.close()
