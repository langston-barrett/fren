#!/usr/bin/env python3
"""Tests of `scripts/heavy`: its argument parsing, the memory cap and the
order of the overrides (the environment variable, then the file in the state
directory, then the default). They use a scratch state directory and fake
memory sizes, and start no job.

    python3 -I scripts/heavy_test.py
"""

import importlib.machinery
import importlib.util
import os
import sys
import tempfile

HERE = os.path.dirname(os.path.realpath(__file__))


def load_heavy():
    path = os.path.join(HERE, "heavy")
    loader = importlib.machinery.SourceFileLoader("heavy", path)
    spec = importlib.util.spec_from_loader("heavy", loader)
    module = importlib.util.module_from_spec(spec)
    loader.exec_module(module)
    return module


heavy = load_heavy()
GB = 1024 * 1024  # KB


def raises(f, kind):
    try:
        f()
    except kind:
        return True
    return False


def test_parse_args():
    p = heavy.parse_args
    assert p(["lake", "build", "--wfail"]) == (False, ["lake", "build", "--wfail"])
    assert p(["--offline", "fuzz", "--offline"]) == (True, ["fuzz", "--offline"])
    assert p(["--", "--offline"]) == (False, ["--offline"])
    assert p(["--offline", "--", "-x"]) == (True, ["-x"])
    for bad in ([], ["--offline"], ["--"], ["--bogus", "ls"], ["-h"]):
        assert raises(lambda: p(bad), heavy.UsageError), bad


def test_physical_memory():
    meminfo = "MemFree:  1000 kB\nMemTotal:       32864960 kB\nSwapTotal: 0 kB\n"
    assert heavy.meminfo_kb(meminfo) == 32864960
    assert raises(lambda: heavy.meminfo_kb("MemFree: 1 kB\n"), ValueError)
    assert heavy.memsize_kb("17179869184\n") == 16 * GB
    with tempfile.NamedTemporaryFile("w", suffix="meminfo") as f:
        f.write(meminfo)
        f.flush()
        assert heavy.physical_memory_kb("Linux", f.name) == 32864960
    assert raises(lambda: heavy.physical_memory_kb("Plan9"), ValueError)


def test_overrides():
    physical = lambda: 20 * GB
    with tempfile.TemporaryDirectory() as state:
        cap = lambda env: heavy.mem_cap_kb(env, state, physical)
        slots = lambda env: heavy.slot_count(env, state)

        # The defaults: 80% of physical memory, and 2 slots.
        assert cap({}) == 16 * GB
        assert slots({}) == 2

        # A file overrides the default, and is re-read on every call.
        with open(os.path.join(state, "mem_gb"), "w") as f:
            f.write("6\n")
        with open(os.path.join(state, "slots"), "w") as f:
            f.write("3\n")
        assert cap({}) == 6 * GB
        assert slots({}) == 3
        with open(os.path.join(state, "mem_gb"), "w") as f:
            f.write("2.5")
        assert cap({}) == int(2.5 * GB)

        # The environment variable overrides the file.
        assert cap({"HEAVY_MEM_GB": "4"}) == 4 * GB
        assert slots({"HEAVY_SLOTS": "1"}) == 1

        # An empty or invalid setting falls through to the next.
        assert cap({"HEAVY_MEM_GB": ""}) == int(2.5 * GB)
        assert cap({"HEAVY_MEM_GB": "lots"}) == int(2.5 * GB)
        assert cap({"HEAVY_MEM_GB": "-1"}) == int(2.5 * GB)
        assert slots({"HEAVY_SLOTS": "0"}) == 3  # 0 slots would never start a job
        with open(os.path.join(state, "mem_gb"), "w") as f:
            f.write("")
        assert cap({}) == 16 * GB
        assert cap({"HEAVY_MEM_GB": "nan"}) == 16 * GB
        os.remove(os.path.join(state, "slots"))
        assert slots({"HEAVY_SLOTS": "x"}) == 2
        assert slots({"HEAVY_SLOTS": "0"}) == 2

        # The default reads the physical memory only when nothing overrides it.
        def unreadable():
            raise AssertionError("read the physical memory")
        assert heavy.mem_cap_kb({"HEAVY_MEM_GB": "1"}, state, unreadable) == GB


def test_offline_command():
    ok = lambda c: True
    no = lambda c: False
    seen = []
    assert heavy.offline_command(["fuzz", "-n", "3"], "Linux", lambda c: seen.append(c) or True) \
        == ["unshare", "-rn", "--", "fuzz", "-n", "3"]
    assert seen == [["unshare", "-rn", "--", "true"]]
    mac = heavy.offline_command(["fuzz"], "Darwin", ok)
    assert mac == ["sandbox-exec", "-p", heavy.MACOS_OFFLINE_PROFILE, "fuzz"]
    assert "(deny network*)" in heavy.MACOS_OFFLINE_PROFILE
    # Where it cannot cut the network, it refuses rather than run online.
    for system in ("Linux", "Darwin"):
        assert raises(lambda: heavy.offline_command(["fuzz"], system, no), RuntimeError)
    assert raises(lambda: heavy.offline_command(["fuzz"], "Plan9", ok), RuntimeError)


def main():
    tests = [test_parse_args, test_physical_memory, test_overrides, test_offline_command]
    for t in tests:
        t()
    print(f"heavy: {len(tests)} tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
