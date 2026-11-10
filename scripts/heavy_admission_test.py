#!/usr/bin/env python3
"""Differential checks of the admission decisions: the start rule, the
priority class and its CPU share, and whose turn a slot is.
Run after building Heavy.Admission: python3 -I scripts/heavy_admission_test.py.
The active Python scheduler is compared with the Std-only Lean kernel on
generated and boundary inputs; no job is started and no state is touched.
"""

from fractions import Fraction
import json
import math
from pathlib import Path
import random
import subprocess
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from heavy_test import heavy

ROOT = Path(__file__).resolve().parent.parent
LABELS = [None, "", "main-repair", "critical-path", "merge-blocking", "edit-loop", "exploratory",
          "Merge-Blocking", "merge-blocking ", "urgent"]
LOADS = [None, 0.0, 0.1, 0.30000000000000004, 0.3, 6.99, 7.0, math.nextafter(7.0, 8.0), 7.5, 64.0]


def scaled(values):
    """The floats as integers in one common unit, exactly."""
    exact = [None if v is None else Fraction(v) for v in values]
    unit = math.lcm(*(v.denominator for v in exact if v is not None), 1)
    return [None if v is None else int(v * unit) for v in exact]


def start_case(rng):
    cap = rng.choice([0, 1, 5, 1000, 16 * 1024 * 1024, 10 ** 17 + 1])
    edge = 3 * cap // 5
    rss = rng.choice([math.inf, 0, edge - 1, edge, edge + 1, cap, rng.randrange(0, 2 * cap + 2)])
    waited = rng.choice([0.0, 299.999, math.nextafter(300.0, 0.0), 300.0, 300.001, rng.uniform(0, 600)])
    limit, load = rng.choice(LOADS[1:] + [None, None]), rng.choice(LOADS)
    if limit == 0.0:
        limit = None  # A limit setting is positive.
    want = heavy.can_start(waited, rss, cap, limit, lambda: load)
    waited_units, grace_units = scaled([waited, float(heavy.LOAD_GRACE_SECONDS)])
    limit_units, load_units = scaled([limit, load])
    return ({"kind": "start", "rss": None if rss == math.inf else rss, "cap": cap, "waited": waited_units,
             "grace": grace_units, "limit": limit_units, "load": load_units}, want)


def class_case(label, writable, outsiders):
    name = heavy.priority_class(label)
    want = {"label": name, "rank": heavy.PRIORITY_CLASSES.index(name), "nice": heavy.PRIORITY_NICE[name],
            "weight": heavy.cpu_weight(label, writable, outsiders)}
    return {"kind": "class", "label": label, "writable": writable, "outsiders": outsiders}, want


def random_waiter(rng, now, step):
    # Enqueue times cluster on multiples of the aging step, so that keys of
    # different classes tie and the sequence decides.
    enqueued = now - rng.choice([0, 1, step, 2 * step, 4 * step, 4 * step + 1, rng.randrange(0, 6 * step + 2)])
    limit = rng.choice(LOADS[1:] + [None, None, None])
    return {"version": 1, "sequence": rng.choice([1, 2, 3, rng.randrange(10 ** 12)]),
            "priority": rng.choice(LABELS), "enqueued_ms": enqueued,
            "updated_ms": now - rng.choice([-1, 0, 0, 1, 5000, heavy.WAITER_STALE_MS - 1, heavy.WAITER_STALE_MS,
                                            heavy.WAITER_STALE_MS + 1]),
            "slots": rng.choice([0, 1, 2, 5, 5, 8]), "cap_kb": rng.choice([0, 1000, 5000, 5000, 16 * 1024 * 1024]),
            "max_load": None if limit == 0.0 else limit}


def turn_case(rng):
    now, step = rng.randrange(10 ** 6, 10 ** 9), rng.choice([0, 1, 1000, 300000])
    own = random_waiter(rng, now, step)
    others = [random_waiter(rng, now, step) for _ in range(rng.randrange(0, 9))]
    slot, load = rng.choice([0, 0, 0, 1, 1, 4, 5, 7]), rng.choice(LOADS)
    rss = rng.choice([math.inf, 0, 0, 600, 601, 3000, 3001, 10 ** 7])
    reader = lambda: load
    before = [heavy.queue_before(w, own, step) for w in others]
    contends = [heavy.queue_contends(w, slot, rss, reader, now) for w in others]
    ahead = heavy.queue_ahead(own, others, slot, rss, reader, now, step)
    assert ahead == sum(1 for b, c in zip(before, contends) if b and c)
    # One common unit for the load and every waiter's limit.
    units = scaled([load] + [w["max_load"] for w in [own] + others])
    wire = lambda w, limit: {"sequence": w["sequence"], "label": w["priority"], "enqueued": w["enqueued_ms"],
                             "updated": w["updated_ms"], "slots": w["slots"], "cap": w["cap_kb"], "limit": limit}
    return ({"kind": "turn", "own": wire(own, units[1]),
             "others": [wire(w, unit) for w, unit in zip(others, units[2:])], "slot": slot,
             "rss": None if rss == math.inf else rss, "load": units[0], "now": now,
             "ttl": heavy.WAITER_STALE_MS, "grace": heavy.LOAD_GRACE_SECONDS * 1000, "step": step},
            {"before": before, "contends": contends, "ahead": ahead, "turn": ahead == 0})


def main():
    rng = random.Random(20261110)
    cases = [start_case(rng) for _ in range(4000)]
    cases += [class_case(label, writable, outsiders)
              for label in LABELS for writable in (False, True) for outsiders in (0, 1, 7)]
    cases += [turn_case(rng) for _ in range(4000)]
    # The generator must reach each outcome, or agreement says little.
    starts = [want for inp, want in cases if inp["kind"] == "start"]
    turns = [want for inp, want in cases if inp["kind"] == "turn"]
    assert 400 < sum(starts) < len(starts) - 400
    assert 400 < sum(t["turn"] for t in turns) < len(turns) - 400
    assert sum(1 for t in turns if t["ahead"] > 1) > 100
    assert sum(1 for t in turns if any(b and not c for b, c in zip(t["before"], t["contends"]))) > 100
    run = subprocess.run(["lake", "env", "lean", "--run", "scripts/heavy_admission_test.lean"],
                         cwd=ROOT, input="".join(json.dumps(inp) + "\n" for inp, _ in cases),
                         text=True, capture_output=True, timeout=300)
    assert run.returncode == 0, run.stdout + run.stderr
    actual = [json.loads(line) for line in run.stdout.splitlines()]
    assert len(actual) == len(cases), (len(actual), len(cases))
    for i, (got, (inp, want)) in enumerate(zip(actual, cases)):
        assert got == want, (i, got, want, inp)
    print(f"{len(starts)} start, {len(cases) - len(starts) - len(turns)} class and "
          f"{len(turns)} turn comparisons agree between Lean and Python")


if __name__ == "__main__":
    main()
