#!/usr/bin/env python3
"""Differential tests for the Std-only forecast kernel and active Python heavy.
Run after building Heavy.Forecast: python3 -I scripts/heavy_forecast_test.py.
"""

import json
import math
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from heavy_test import heavy

ROOT = Path(__file__).resolve().parent.parent


def transport(lines, key, now, seconds, n):
    """Decode fields, leaving eligibility, order, truncation and max to Lean.
    Exact binary ratios avoid rounding timestamps at either cutoff boundary.
    """
    rows = []
    for line in lines:
        try:
            row = json.loads(line)
        except (ValueError, UnicodeError):
            continue
        if not isinstance(row, dict):
            continue
        ended = row.get("ended_at")
        try:
            valid_time = type(ended) in (int, float) and math.isfinite(ended)
        except OverflowError:
            valid_time = False
        peak = row.get("peak_rss_kb")
        rows.append({"event": row.get("event", "job"), "key": row.get("job_kind"),
                     "ended": ended if valid_time else None,
                     "peak": peak if type(peak) is int else None})
    times = [now, now - seconds] + [r["ended"] for r in rows if r["ended"] is not None]
    scale = max(t.as_integer_ratio()[1] for t in times)

    def ticks(t):
        a, b = t.as_integer_ratio()
        return a * (scale // b)

    for row in rows:
        if row["ended"] is not None:
            row["ended"] = ticks(row["ended"])
    return {"history": rows, "key": key, "cutoff": ticks(now - seconds),
            "now": ticks(now), "n": n}


def job(t, p, **extra):
    return json.dumps({"job_kind": "k", "ended_at": t, "peak_rss_kb": p, **extra})


def main():
    cases = []

    def add(lines, key="k", now=100, seconds=10, n=20, expected=None):
        cases.append((lines, key, now, seconds, n, expected))

    add([], expected=(None, 0))
    add([job(90, 7), job(100, 8), job(89.99999999999999, 999),
         job(100.00000000000001, 999)], expected=(8, 2))
    add([job(89, 999), job(101, 999)], expected=(None, 0))
    add([job(95, 10, exit_code=137)], expected=(10, 1))
    add([job(95, 10)], n=0, expected=(None, 0))
    add([job(95, 10)], key="unknown", expected=(None, 0))
    # Unsorted log order, an old large peak, duplicates and ties at last-N.
    add([job(91, 999), job(94, 3), job(93, 4), job(92, 5)], n=2, expected=(4, 2))
    add([job(95, 9), job(95, 3), job(95, 8), job(95, 9)], n=2, expected=(9, 2))
    add([job(95, 9), job(95, 3), job(95, 8)], n=1, expected=(9, 1))
    add([job(95, 8), job(95, 3), job(95, 9)], n=1, expected=(9, 1))
    add([job(95, 4), "null", "[]", "{}", '{"partial":', b"\xff",
         '{"job_kind":"k","ended_at":95}', '{"job_kind":"k","peak_rss_kb":999}',
         '{"ended_at":95,"peak_rss_kb":999}',
         job(True, 999), job("95", 999), job(None, 999), job(float("nan"), 999),
         job(float("inf"), 999), job(10 ** 1000, 999), job(95, True), job(95, 0),
         job(95, -1), job(95, 999.0), job(95, None), job(95, "999"),
         job(95, 999, event="sample"), job(95, 999, event=None),
         job(95, 999, event=42)], expected=(4, 1))
    add([job(95, 9), job(96, 8)], seconds=0, expected=(None, 0))
    add([job(100, 9)], seconds=0, expected=(9, 1))
    add([job(100, 9)], seconds=-1, expected=(None, 0))
    recorded = (ROOT / "test/heavy/forecast.jsonl").read_text().splitlines()
    rows = [json.loads(line) for line in recorded]
    # Every recorded prefix, with production limits and varying windows.
    for i, row in enumerate(rows, 1):
        add(recorded[:i], row["job_kind"], row["ended_at"], heavy.PREDICTION_SECONDS)
    for key in sorted({r["job_kind"] for r in rows}):
        for n in (0, 1, 3, 20):
            add(list(reversed(recorded)), key, max(r["ended_at"] for r in rows), 3600, n)
    inputs, expected = [], []
    with tempfile.TemporaryDirectory() as state:
        path = os.path.join(state, "log.jsonl")
        for lines, key, now, seconds, n, fixed in cases:
            with open(path, "wb") as log:
                for line in lines:
                    log.write((line.encode() if isinstance(line, str) else line) + b"\n")
            with mock.patch.object(heavy, "PREDICTION_SECONDS", seconds), \
                 mock.patch.object(heavy, "PREDICTION_JOBS", n):
                result = heavy.predict_peak_rss(key, state, {}, now)
            if fixed is not None:
                assert result == fixed, (lines, result, fixed)
            expected.append(list(result))
            inputs.append(transport(lines, key, now, seconds, n))
    run = subprocess.run(["lake", "env", "lean", "--run", "scripts/heavy_forecast_test.lean"],
                         cwd=ROOT, input="".join(json.dumps(j) + "\n" for j in inputs),
                         text=True, capture_output=True, timeout=120)
    assert run.returncode == 0, run.stdout + run.stderr
    actual = [json.loads(line) for line in run.stdout.splitlines()]
    assert len(actual) == len(expected), (len(actual), len(expected))
    for i, (got, want) in enumerate(zip(actual, expected)):
        assert got == want, (i, got, want, inputs[i])
    print(f"{len(cases)} Lean/Python forecasts agree (320 recorded observations)")


if __name__ == "__main__":
    main()
