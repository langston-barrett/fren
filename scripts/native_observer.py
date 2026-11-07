"""Live, bounded observations of this runner's owned processes only."""
import hashlib
import itertools
import json
import os
from pathlib import Path
import time

from native_test_process import children, identity


def save(path, value):
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def read(path):
    try:
        return json.loads(path.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def tail(path, size=16384):
    try:
        with path.open("rb") as stream:
            stream.seek(max(0, os.fstat(stream.fileno()).st_size - size))
            return stream.read(size).decode(errors="replace")
    except FileNotFoundError:
        return ""


def emit(env, event, **fields):
    path = env.get("FREN_NATIVE_LIVE_FILE")
    if path:
        # One bounded append, shared by nested runners. No environment or
        # captured checker output is copied into the live channel.
        row = json.dumps({"native": event, "observer_pid": os.getpid(), **fields},
                         separators=(",", ":"))
        if len(row) > 3072:
            row = json.dumps({"native": event, "observer_pid": os.getpid(),
                              "excerpt": row[:2048], "truncated": True})
        fd = os.open(path, os.O_WRONLY | os.O_APPEND)
        try:
            os.write(fd, (row + "\n").encode())
        finally:
            os.close(fd)


def invocation(command, cohort, workers):
    raw = json.dumps(command, separators=(",", ":"))
    return {"argv_excerpt": raw[:1024], "argv_sha256": hashlib.sha256(raw.encode()).hexdigest(),
            "cohort_sha256": hashlib.sha256(json.dumps(cohort).encode()).hexdigest(),
            "cohort_size": len(cohort), "workers": workers}


def snapshot():
    # /proc contains only readings, never executable commands or environment.
    # Bound traversal, text sizes, thread count and elapsed observation work.
    deadline = time.monotonic() + 1
    pending = [os.getpid()]
    rows = []
    truncated = False
    for parent in pending:
        for pid in children(parent):
            if len(rows) == 64 or time.monotonic() >= deadline:
                truncated = True
                break
            observed = identity(pid)
            if not observed or observed[0] != parent:
                continue
            pending.append(pid)
            row = {"pid": pid, "ppid": parent, "starttime": observed[1], "threads": []}
            try:
                for thread in itertools.islice(Path(f"/proc/{pid}/task").iterdir(), 32):
                    if time.monotonic() >= deadline:
                        truncated = True
                        break
                    fields = tail(thread / "stat", 4096).rsplit(")", 1)[-1].split()
                    row["threads"].append({"tid": int(thread.name),
                        "state": fields[0] if fields else "unavailable",
                        "cpu_ticks": fields[11:13], "wchan": tail(thread / "wchan", 128)})
            except (FileNotFoundError, ProcessLookupError):
                row["raced_exit"] = True
            rows.append(row)
        if truncated:
            break
    return {"owned": rows, "truncated": truncated,
            "platform": "linux-proc" if Path("/proc/self").exists() else "unavailable"}
