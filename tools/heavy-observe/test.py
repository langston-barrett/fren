#!/usr/bin/env python3
"""Owned, bounded Linux integration tests. Build standalone targets first.
Run this harness through scripts/heavy --offline. Evidence remains in test-work.
No network, external process signals, shared cache mutation or admission change.
"""

from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import statistics
import sys
import subprocess
import tempfile
import time

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from owned_test import run as owned_run
from overlay import create
from abi_check import check as check_abi
from regressions import file_controls, metadata_controls, metadata_reuse_controls

HERE = Path(__file__).resolve().parent
# Test-only discovery; the launcher itself always uses explicit configuration.
OBSERVER = HERE / ".lake/build/bin/heavy_observe"


def main():
    args = sys.argv[1:]
    parts = {"publisher", "forecast", "entrypoint", "cohort", "core",
             "automatic", "automaticEvidence", "automaticStore", "automaticIO", "automaticOwnership"}
    if args in ([], ["--controls-only"]):
        selected = parts
    elif len(args) == 2 and args[0] == "--part" and args[1] in parts:
        selected = {args[1]}
    else:
        raise SystemExit("usage: test.py [--controls-only | --part {publisher,forecast,entrypoint,cohort,core,automatic,automaticEvidence,automaticStore,automaticIO,automaticOwnership}]")
    def modules(mode):
        fresh = Path(tempfile.mkdtemp(prefix="heavy-module-partition-"))
        env = dict(os.environ, HEAVY_MODULE_TEST_ROOT=str(fresh / "test-work"))
        owned_run([sys.executable, "-I", str(HERE / "module_memory_test.py"), mode],
                  directory=fresh, label="module-dispatch", env=env,
                  timeout=15, grace=3, check=True)
    # Preparation's foreign-member control must run before this job migrates.
    if "automaticIO" in selected: modules("negative")
    for part, script in (("publisher", "publish_test.py"), ("forecast", "forecast_test.py"),
                         ("entrypoint", "entrypoint_test.py")):
        if part in selected:
            dispatch = Path(tempfile.mkdtemp(prefix="heavy-process-dispatch-"))
            owned_run([sys.executable, "-I", str(HERE / script)], directory=dispatch,
                      label="dispatch", timeout=30, grace=5, check=True)
    for part, mode in (("automatic", "positive"), ("automaticEvidence", "evidence"),
                       ("automaticStore", "store"), ("automaticIO", "io"),
                       ("automaticOwnership", "ownership")):
        if part in selected:
            # Every registered partition starts in its own empty fixture tree.
            # The child, not another test group, creates test-work itself.
            fresh = Path(tempfile.mkdtemp(prefix="heavy-automatic-partition-"))
            env = dict(os.environ, HEAVY_AUTOMATIC_TEST_ROOT=str(fresh / "test-work"),
                       HEAVY_AUTOMATIC_REQUIRE_FRESH="1")
            script = "automatic_test.py" if mode in ("positive", "evidence", "store") else "automatic_io_test.py"
            owned_run([sys.executable, "-I", str(HERE / script), mode], directory=fresh,
                      label="dispatch", env=env, timeout=23, grace=5, check=True)
    if "cohort" in selected: modules("directRun")
    if "entrypoint" in selected:
        modules("direct")
        modules("producer")
    if not ({"cohort", "core"} & selected): return
    (HERE / "test-work").mkdir(exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="run-", dir=HERE / "test-work"))
    if "cohort" in selected:
        owned_run([sys.executable, "-I", str(HERE / "cohort_gate_test.py"),
                   str(work / "cohort-gate")], directory=work, label="cohort-dispatch",
                  timeout=20, grace=5, check=True)
    if "core" not in selected: return
    configured = os.environ.get("HEAVY_TEST_REAL_LEAN")
    if configured is None:
        prefix = owned_run(["lean", "--print-prefix"], directory=work, label="prefix",
                           timeout=3, check=True).stdout.decode().strip()
        configured = prefix + "/bin/lean"
    REAL = Path(configured).resolve(strict=True)
    overlay = create(work / "overlay", REAL, OBSERVER)
    records = overlay / "records"
    shim = overlay / "bin/lean"
    env = {**os.environ, "LAKE_ARTIFACT_CACHE": "false", "LAKE_RESTORE_ARTIFACTS": "false",
           "LAKE_NO_CACHE": "true", "HEAVY_OBSERVE_DIR": str(records)}
    env.pop("LEAN_SYSROOT", None)
    env.pop("LAKE_OVERRIDE_LEAN", None)
    env.pop("LEAN", None)
    timings = []
    abi = check_abi(HERE, REAL, work)
    assert abi["status"] == 0, (work / "abi-check.log").read_text()

    def run(command, *, cwd=work, variables=None, stdin=None):
        start = time.monotonic()
        child = subprocess.Popen(list(map(str, command)), cwd=cwd, env=variables or env,
            stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        try:
            stdout, stderr = child.communicate(stdin, timeout=15)
        except subprocess.TimeoutExpired:
            # This session and every process in it belong to this test call.
            os.killpg(child.pid, signal.SIGKILL)
            child.communicate()
            raise AssertionError(f"owned test timed out: {command}")
        p = subprocess.CompletedProcess(command, child.returncode, stdout, stderr)
        timings.append({"command": list(map(str, command)), "seconds": time.monotonic() - start,
                        "status": p.returncode})
        return p

    def rows():
        return [json.loads(p.read_text()) for p in sorted(records.glob("process-*.json"))]

    def compare(args, *, stdin=None):
        ordinary = run([REAL, *args], stdin=stdin)
        observed = run([shim, *args], stdin=stdin)
        assert (observed.returncode, observed.stdout, observed.stderr) == (
            ordinary.returncode, ordinary.stdout, ordinary.stderr), (args, ordinary, observed)
        return observed

    pure = run([HERE / ".lake/build/bin/process_tests"])
    assert pure.returncode == 0, pure.stderr
    lines = pure.stdout.decode().splitlines()
    assert len(lines) == 65536
    for line in lines:
        status, kind, detail, shell = map(int, line.split())
        if os.WIFEXITED(status):
            expected = (0, os.WEXITSTATUS(status), os.WEXITSTATUS(status))
        elif os.WIFSIGNALED(status):
            sig = os.WTERMSIG(status)
            expected = (1, sig, 128 + sig)
        else:
            expected = (3, 0, 125)
        assert (kind, detail, shell) == expected, line

    for probe in ("--version", "--githash", "--print-prefix", "--help"):
        compare([probe])
    (work / "Exit.lean").write_text('''import Std
 def main (args : List String) : IO UInt32 := do
   IO.println (repr args)
   IO.println (← IO.getEnv "OBSERVER_SENTINEL")
   IO.print (← (← IO.getStdin).getLine)
   (← IO.getStderr).putStrLn "stderr sentinel"
   return 7
'''.replace('\n def', '\ndef').replace('\n   ', '\n  '))
    env["OBSERVER_SENTINEL"] = 'spaces " slash \\ Unicode λ\nline'
    weird_args = ["--run", "Exit.lean", "space argument", '"\\\n\tλ',
                  "-o", "program-data", "-i", "ignored", "-c", "/dev/stdout", "-b", "ignored",
                  "--setup", "program-setup.json", "other.lean"]
    assert compare(weird_args, stdin=b"inherited stdin\n").returncode == 7
    exit_row = [r for r in rows() if r["args"] == weird_args][-1]
    assert (exit_row["result_kind"], exit_row["result_detail"], exit_row["raw_wait_status"]) == (0, 7, 7 << 8)
    assert exit_row["source"] == "Exit.lean" and exit_row["artifacts"] == [] and exit_row["setup"] is None
    assert exit_row["source_before"] and not exit_row["identity_complete"] and exit_row["input_closure"] is None
    (work / "Bad.lean").write_text('def broken : Nat := "wrong type"\n')
    assert compare(["Bad.lean"]).returncode == 1

    # The real Lean compiler signals only itself, via a helper it owns.
    (work / "Signal.lean").write_text('''import Std
 def main : IO Unit := do
   let pid ← IO.Process.getPID
   let p ← IO.Process.spawn {cmd := "/bin/sh", args := #["-c", s!"kill -TERM {pid}"]}
   let _ ← p.wait
   IO.sleep 1000
'''.replace('\n def', '\ndef').replace('\n   ', '\n  '))
    assert compare(["--run", "Signal.lean"]).returncode == -15
    signal_row = [r for r in rows() if r["source"] == "Signal.lean"][-1]
    assert (signal_row["result_kind"], signal_row["result_detail"], signal_row["shell_code"]) == (1, 15, 143)

    # A recording failure preserves a real child's exit and streams, with an explicit warning.
    unavailable = work / "not-a-directory"
    unavailable.write_text("owned negative control")
    failed_log = run([shim, *weird_args], variables={**env, "HEAVY_OBSERVE_DIR": str(unavailable)}, stdin=b"inherited stdin\n")
    assert failed_log.returncode == 7 and b"record failed" in failed_log.stderr
    assert b"stderr sentinel" in failed_log.stderr
    # Even failure to print the observer warning must preserve the child result.
    with open("/dev/full", "wb") as full:
        silent_warning = subprocess.run([str(shim), "--version"], cwd=work,
            env={**env, "HEAVY_OBSERVE_DIR": str(unavailable)}, stdout=subprocess.PIPE,
            stderr=full, timeout=10)
    assert silent_warning.returncode == 0


    negative = work / "negative"
    (negative / "bin").mkdir(parents=True)
    shutil.copy2(OBSERVER, negative / "bin/lean")
    negative_shim = negative / "bin/lean"
    config = negative / "real-lean.path"
    config.write_text(str(work / "missing-compiler") + "\n")
    missing = run([negative_shim, "--version"])
    assert missing.returncode == 127 and b"exec failed (errno 2)" in missing.stderr
    assert any(r["exec_errno"] == 2 and r["result_kind"] == 2
               and r["measured_cpu_us"] is None and r["measured_peak_rss_kib"] is None for r in rows())
    for target in (negative_shim, OBSERVER):
        config.write_text(str(target) + "\n")
        recursive = run([negative_shim, "--version"])
        assert recursive.returncode == 125 and b"recursive overlay" in recursive.stderr
    try:
        create(work / "recursive", OBSERVER, OBSERVER)
    except ValueError as e:
        assert "recursive overlay" in str(e)
    else:
        raise AssertionError("overlay setup accepted observer as compiler")

    # Actual special files must not be consumed or reopened by fingerprinting.
    (work / "Special.lean").write_text('def specialValue : Nat := 3\n')
    for output in ("/dev/stdout", "/dev/null"):
        assert compare(["Special.lean", "-c", output]).returncode == 0
        assert all(r["artifacts"][0]["fingerprint"] is None for r in rows()
                   if r["args"] == ["Special.lean", "-c", output])
    file_evidence = file_controls(work, REAL, shim, HERE / ".lake/build/bin/process_tests", run)
    metadata_evidence = metadata_controls(work, compare, rows)
    output_fifo = work / "output.c"
    os.mkfifo(output_fifo)
    def with_output_fifo(exe):
        reader = subprocess.Popen([sys.executable, "-c",
            "import sys; sys.stdout.buffer.write(open(sys.argv[1], 'rb').read())", str(output_fifo)],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            result = run([exe, "Special.lean", "-c", str(output_fifo)])
            data, error = reader.communicate(timeout=2)
            assert reader.returncode == 0 and not error
            return result, data
        finally:
            if reader.poll() is None:
                reader.kill(); reader.wait()
    (plain_output, plain_data), (observed_output, observed_data) = with_output_fifo(REAL), with_output_fifo(shim)
    assert plain_output.returncode == observed_output.returncode == 0
    assert (plain_output.stdout, plain_output.stderr, plain_data) == (
        observed_output.stdout, observed_output.stderr, observed_data)
    assert any(r["args"] == ["Special.lean", "-c", str(output_fifo)]
               and r["artifacts"][0]["fingerprint"] is None for r in rows())
    oversized = work / "oversized"
    with oversized.open("wb") as f:
        f.truncate(67108865)
    assert compare(["Bad.lean", "-o", str(oversized)]).returncode == 1
    assert any(r["args"] == ["Bad.lean", "-o", str(oversized)]
               and r["artifacts"][0]["fingerprint"] is None for r in rows())

    reuse_evidence = metadata_reuse_controls(work, OBSERVER)

    if "--controls-only" in sys.argv:
        report = {"work": str(work), "abi": abi, "file_controls": file_evidence,
                  "metadata_controls": metadata_evidence, "metadata_reuse_controls": reuse_evidence,
                  "checks": "controls passed", "timings": timings}
        (work / "controls-report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(str(work / "controls-report.json"))
        return

    # Exactly one scratch experiment: same 3-module graph and output paths,
    # clean local build artifacts before each side; no cache downloads/restores.
    scratch = work / "scratch"
    (scratch / "Measure").mkdir(parents=True)
    (scratch / "lakefile.toml").write_text('name = "observerScratch"\n[[lean_lib]]\nname = "Measure"\n')
    shutil.copy2(HERE / "lean-toolchain", scratch / "lean-toolchain")
    (scratch / "Measure/Base.lean").write_text('''import Std
namespace Measure
 def values : List Nat := (List.range 4000).map (fun n => n * n + 1)
 theorem values_length : values.length = 4000 := by simp [values]
end Measure
'''.replace('\n def', '\ndef').replace('\n theorem', '\ntheorem'))
    (scratch / "Measure/Map.lean").write_text('''import Measure.Base
set_option maxRecDepth 100000
namespace Measure
 def total : Nat := values.foldl (· + ·) 0
 theorem total_positive : total > 0 := by decide
end Measure
'''.replace('\n def', '\ndef').replace('\n theorem', '\ntheorem'))
    (scratch / "Measure.lean").write_text('import Measure.Map\n#eval Measure.total\nexample : Measure.values.length = 4000 := Measure.values_length\n')
    lake = REAL.parent / "lake"
    ordinary = run([lake, "-q", "build", "Measure"], cwd=scratch)
    assert ordinary.returncode == 0, ordinary.stderr
    def artifacts():
        return {str(p.relative_to(scratch)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in (scratch / ".lake/build").rglob("*") if p.suffix in (".olean", ".ilean", ".c", ".ir")}
    ordinary_artifacts = artifacts()
    shutil.rmtree(scratch / ".lake/build")
    before = {p.name for p in records.iterdir()}
    overlay_env = {**env, "LAKE_OVERRIDE_LEAN": "true", "LEAN_SYSROOT": str(overlay)}
    # Explicit source-bound synthetic requests: not calibrated forecasts.
    manifest = work / "budget-requests"
    request_rows = []
    for source, demand in [(scratch / "Measure/Base.lean", 900000),
                           (scratch / "Measure/Map.lean", 1100000),
                           (scratch / "Measure.lean", 700000)]:
        digest = run([HERE / ".lake/build/bin/process_tests", "--read", source]).stdout.decode().strip().removeprefix("some:")
        request_rows.append(f"{source}\tlean-bytearray64:{source.stat().st_size}:{digest}\t{demand}\n")
    manifest.write_text("".join(request_rows))
    gated_command = [HERE / ".lake/build/bin/budget_session", work / "budget-session", "1300000", "100000", "1200000", "5000",
                     manifest, "--", lake, "-q", "build", "Measure"]
    observed = run(gated_command, cwd=scratch, variables=overlay_env)
    gated_seconds = timings[-1]["seconds"]
    assert (observed.returncode, observed.stdout, observed.stderr) == (
        ordinary.returncode, ordinary.stdout, ordinary.stderr), (ordinary, observed)
    assert artifacts() == ordinary_artifacts, "compiler artifacts differ"
    build_rows = [json.loads(p.read_text()) for p in records.glob("process-*.json") if p.name not in before]
    compilers = [r for r in build_rows if r["source"] is not None]
    assert len(compilers) == 3, build_rows
    assert {Path(r["source"]).name for r in compilers} == {"Base.lean", "Map.lean", "Measure.lean"}
    for r in compilers:
        assert r["gate_errno"] == 0 and r["child_present"] and r["schema"] == 3
        assert r["requested_reservation_kib"] > 0 and r["request_provenance"] == "explicit-source-request"
        assert r["parent_headroom_kib"] + r["held_before_kib"] + r["requested_reservation_kib"] <= r["allowance_kib"]
        assert r["result_kind"] == 0 and r["result_detail"] == 0
        assert r["peak_rss_kib"] > 0 and r["wall_ns"] > 0
        assert r["wall_ns"] == r["end_monotonic_ns"] - r["start_monotonic_ns"]
        assert r["user_us"] + r["system_us"] > 0
        assert r["measured_cpu_us"] == r["user_us"] + r["system_us"]
        assert r["measured_peak_rss_kib"] == r["peak_rss_kib"]
        assert r["source_before"] == r["source_after"] and r["source_before"]
        assert r["setup_fingerprint"] and r["artifacts"]
        assert all(a["fingerprint"] for a in r["artifacts"])
        assert not r["identity_complete"] and r["input_closure"] is None
        assert r["real_compiler"] == str(REAL) and r["compiler_githash"]

    # Changed source gives a changed partial fingerprint; no claim of closure completeness.
    (work / "Change.lean").write_text('def x : Nat := 1\n')
    compare(["Change.lean"])
    first = [r for r in rows() if r["source"] == "Change.lean"][-1]["source_before"]
    (work / "Change.lean").write_text('def x : Nat := 2\n')
    compare(["Change.lean"])
    changed = [r for r in rows() if r["source"] == "Change.lean"]
    assert len({r["source_before"] for r in changed}) == 2 and first

    # Bounded warm-input direct compiler pairs: same cwd, args and output path.
    # The scratch dependency artifacts above stay built. Alternate order.
    pairs = []
    command = ["Measure.lean", "-o", str(scratch / "measured.olean")]
    direct_env = {**env, "LEAN_PATH": str(scratch / ".lake/build/lib/lean")}
    for i in range(3):
        samples = {}
        for name, exe in (("ordinary", REAL), ("observed", shim)) if i % 2 == 0 else (("observed", shim), ("ordinary", REAL)):
            p = run([exe, *command], cwd=scratch, variables=direct_env)
            assert p.returncode == 0, p.stderr
            samples[name] = timings[-1]["seconds"]
        pairs.append(samples)
    # Concurrent publication and ordinary discovery forwarding.
    before = len(rows())
    with ThreadPoolExecutor(max_workers=3) as pool:
        concurrent = list(pool.map(lambda _: run([shim, "--version"]), range(3)))
    assert all(p.returncode == 0 for p in concurrent) and len(rows()) == before + 3
    assert not list(records.glob(".process-*"))
    report = {"work": str(work), "real_compiler": str(REAL), "compiler_version": compilers[0]["compiler_version"],
              "abi": abi, "file_controls": file_evidence, "metadata_controls": metadata_evidence,
              "metadata_reuse_controls": reuse_evidence,
              "raw_status_cases": len(lines), "checks": "all passed", "compiler_records": compilers,
              "scratch_ordinary_s": next(t["seconds"] for t in timings if t["command"] == [str(lake), "-q", "build", "Measure"]),
              "scratch_gated_s": gated_seconds,
              "synthetic_request_manifest": str(manifest),
              "scratch_manifest_sha256": hashlib.sha256((scratch / "lake-manifest.json").read_bytes()).hexdigest(),
              "warm_direct_pairs_s": pairs,
              "median_paired_overhead_s": statistics.median(p["observed"] - p["ordinary"] for p in pairs),
              "artifact_sha256": ordinary_artifacts, "timings": timings}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in ("compiler_records", "timings", "artifact_sha256")}, indent=2))


if __name__ == "__main__":
    main()
