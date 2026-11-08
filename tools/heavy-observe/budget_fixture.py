#!/usr/bin/python3
"""Owned deterministic exec fixture; KiB requests are synthetic decisions."""
import json
import os
import signal
from pathlib import Path
import sys
import time

if sys.argv[1:] == ["--version"]:
    print("owned compiler fixture")
elif sys.argv[1:] == ["--githash"]:
    print("synthetic-request-fixture")
else:
    source = Path(sys.argv[1])
    event = Path(os.environ["BUDGET_EVENTS"]) / source.stem
    event.with_suffix(".start").write_text(json.dumps({"pid": os.getpid(), "ns": time.monotonic_ns()}))
    limit = time.monotonic() + 6
    while not event.with_suffix(".release").exists():
        if time.monotonic() > limit:
            raise SystemExit(124)
        time.sleep(.005)
    if os.environ.get("BUDGET_FORK") and source.stem == "A":
        child = os.fork()
        if child == 0:
            for fd in (0, 1, 2):
                os.close(fd)
            event.with_suffix(".descendant").write_text(str(os.getpid()))
            time.sleep(5)
            os._exit(0)
    event.with_suffix(".end").write_text(str(time.monotonic_ns()))
    print("stdout " + source.stem)
    if source.stem != "Closed":
        print("stderr " + source.stem, file=sys.stderr)
    if source.stem == "Signal":
        sys.stdout.flush()
        sys.stderr.flush()
        os.kill(os.getpid(), signal.SIGTERM)
    raise SystemExit(7 if source.stem == "Exit" else 0)
