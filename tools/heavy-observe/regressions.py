"""Actual pinned-compiler and synchronized owned-file controls for review findings."""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
from unittest.mock import patch

from overlay import regular_bytes


def blocked_writer(path):
    p = subprocess.Popen([sys.executable, "-c",
        "import sys; f=open(sys.argv[1],'wb'); f.write(b'def fifoValue : Nat := 4\\n'); f.close()",
        str(path)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
    try:
        wait_blocked(p)
        return p
    except BaseException:
        cleanup(p)
        raise


def wait_blocked(p):
    end = time.monotonic() + 3
    while time.monotonic() < end:
        assert p.poll() is None, "producer exited before reader rendezvous"
        if Path(f"/proc/{p.pid}/wchan").read_text().strip() == "wait_for_partner":
            return
        time.sleep(.002)
    raise AssertionError("owned writer did not reach wait_for_partner")


def still_blocked(p):
    # Reject schedules that merely check poll before an awakened writer runs.
    for _ in range(20):
        wait_blocked(p)
        time.sleep(.005)


def cleanup(p):
    if p.poll() is None:
        os.killpg(p.pid, signal.SIGKILL)
    p.communicate()


def file_controls(work, real, shim, probe, run):
    evidence = []
    fifo = work / "Synchronized.lean"
    os.mkfifo(fifo)
    for name, exe in (("ordinary", real), ("observed", shim)):
        writer = blocked_writer(fifo)
        try:
            result = run([exe, str(fifo)])
            _, error = writer.communicate(timeout=2)
            assert result.returncode == writer.returncode == 0, (result, error)
            evidence.append({"case": name, "before": "wait_for_partner", "child": 0, "writer": 0})
        finally:
            cleanup(writer)
    # All runtime fingerprint roles share this exact reader, including copy
    # checks. Exercise it directly, in addition to the full source invocation.
    for role in ("source-before", "source-after", "setup", "compiler", "olean", "ilean", "c", "bc", "recursion-self", "recursion-real"):
        candidate = work / (role + ".fifo")
        os.mkfifo(candidate)
        writer = blocked_writer(candidate)
        try:
            result = run([probe, "--read", str(candidate)])
            assert result.returncode == 0 and result.stdout == b"none\n", result
            still_blocked(writer)
            evidence.append({"reader_role": role, "before_after": "wait_for_partner", "fingerprint": None})
        finally:
            cleanup(writer)
    for role in ("helper-real", "helper-observer"):
        candidate = work / (role + ".fifo")
        os.mkfifo(candidate)
        writer = blocked_writer(candidate)
        try:
            try:
                regular_bytes(candidate)
            except ValueError:
                pass
            else:
                raise AssertionError("setup accepted a FIFO")
            still_blocked(writer)
            evidence.append({"reader_role": role, "before_after": "wait_for_partner"})
        finally:
            cleanup(writer)
    # Swap the actual pathname immediately after the actual O_PATH acquisition.
    # No fabricated stat/eligibility or read result is supplied.
    original, replacement = work / "pinned", work / "replacement"
    original.write_bytes(b"original pinned bytes")
    replacement.write_bytes(b"replacement pathname bytes")
    actual_open = os.open
    def swap_after_pin(path, flags, *args, **kwargs):
        fd = actual_open(path, flags, *args, **kwargs)
        if Path(path) == original and flags & os.O_PATH:
            os.replace(replacement, original)
        return fd
    with patch("os.open", swap_after_pin):
        assert regular_bytes(original) == b"original pinned bytes"
    assert original.read_bytes() == b"replacement pathname bytes"
    evidence.append({"pathname_replaced_after_pin": True, "read_original_inode": True})
    return evidence


def metadata_controls(work, compare, rows):
    evidence = []
    (work / "Meta.lean").write_text('def metaValue : Nat := 5\n')
    # First setup is invalid: success proves the later setting took effect.
    (work / "first.json").write_text('invalid setup sentinel')
    setup = {"name": "Meta", "isModule": False, "plugins": [], "dynlibs": [], "options": {}, "importArts": {}}
    for name in ("last.json", "--version"):
        (work / name).write_text(json.dumps(setup))
    args = ["Meta.lean"]
    final = []
    for flag, ext in (("-o", "olean"), ("-i", "ilean"), ("-c", "c")):
        old, new = "unused." + ext, "actual." + ext
        (work / old).write_bytes(b"OLD UNWRITTEN OUTPUT")
        args += [flag, old, flag, new]
        final.append(new)
    args += ["--setup", "first.json", "--setup", "last.json"]
    result = compare(args)
    assert result.returncode == 0, result
    r = next(r for r in rows() if r["args"] == args)
    assert r["source"] == "Meta.lean" and r["input_kind"] == "file"
    assert [a["path"] for a in r["artifacts"]] == final and all(a["fingerprint"] for a in r["artifacts"])
    assert r["setup"] == "last.json" and r["setup_fingerprint"]
    for name in final:
        assert (work / name).stat().st_size > 0
        assert (work / name.replace("actual", "unused")).read_bytes() == b"OLD UNWRITTEN OUTPUT"
    evidence.append({"repeated_o_i_c_setup": args, "status": 0, "effective": final + [r["setup"]]})
    # This pinned build has LLVM disabled. --run still parses the repeated
    # -b settings, and bypasses backend emission (Shell.runMain returns first).
    bc_args = ["-b", "unused.bc", "-b", "actual.bc", "--run", "Exit.lean"]
    (work / "unused.bc").write_bytes(b"OLD UNWRITTEN OUTPUT")
    result = compare(bc_args, stdin=b"input\n")
    assert result.returncode == 7
    r = next(r for r in rows() if r["args"] == bc_args)
    assert [a["path"] for a in r["artifacts"]] == ["actual.bc"]
    assert r["artifacts"][0]["fingerprint"] is None
    assert (work / "unused.bc").read_bytes() == b"OLD UNWRITTEN OUTPUT"
    evidence.append({"repeated_bc": bc_args, "status": 7, "emission_not_claimed": True})
    # Each operand looks like an option; it must never be reconsidered as one.
    for flag, operand in (("-o", "--run"), ("-i", "-o"), ("-c", "-i"), ("--setup", "--version")):
        args = ["Meta.lean", flag, operand]
        result = compare(args)
        assert result.returncode == 0, result
        r = next(r for r in rows() if r["args"] == args)
        assert r["source"] == "Meta.lean" and r["input_kind"] == "file"
        if flag == "--setup":
            assert r["setup"] == operand and r["artifacts"] == []
        else:
            assert [a["path"] for a in r["artifacts"]] == [operand]
            assert (work / operand).stat().st_size > 0
        evidence.append({"operand_case": args, "status": 0})
    bc_operand = ["-b", "-c", "--run", "Exit.lean"]
    assert compare(bc_operand, stdin=b"input\n").returncode == 7
    r = next(r for r in rows() if r["args"] == bc_operand)
    assert [a["path"] for a in r["artifacts"]] == ["-c"] and r["source"] == "Exit.lean"
    evidence.append({"operand_case": bc_operand, "status": 7, "emission_not_claimed": True})
    (work / "Label.lean").write_text('invalid disk sentinel\n')
    for args in (["--stdin", "Label.lean"], ["--stdin"]):
        result = compare(args, stdin=b'def fromStdin : Nat := 8\n')
        assert result.returncode == 0
        r = next(r for r in rows() if r["args"] == args)
        assert r["input_kind"] == "stdin" and r["source"] is None and r["source_before"] is None and r["source_after"] is None and r["module_hint"] is None
        evidence.append({"stdin_case": args, "no_disk_source": True})
    for args in (["--version", "Meta.lean"], ["Meta.lean", "--version"], ["--print-prefix", "Meta.lean"], ["--help", "-o", "unused.olean"]):
        result = compare(args)
        assert result.returncode == 0
        r = next(r for r in rows() if r["args"] == args)
        assert r["input_kind"] == "query" and r["artifacts"] == []
        assert all(r[key] is None for key in ("source", "source_before", "source_after", "module_hint", "setup", "setup_fingerprint"))
        evidence.append({"discovery_case": args, "no_compile_fields": True})
    # Pinned compiler supports these forms, but this intentionally conservative
    # metadata parser does not. Confirm real effects, never infer a disk source.
    for args, output in ((["Meta.lean", "--o=long.olean"], "long.olean"),
                         (["Meta.lean", "-oattached.olean"], "attached.olean"),
                         (["Meta.lean", "--c=long.c"], "long.c"),
                         (["--", "Meta.lean", "-o", "boundary.olean"], None),
                         (["Meta.lean", "--setup=last.json"], None),
                         (["--o=looks.lean"], None),
                         (["-I", "Label.lean"], None),
                         (["-D", "invalid", "Meta.lean"], None),
                         (["-D", "weak.fren.runChecks=false", "Meta.lean"], None),
                         (["Meta.lean", "-o"], None),
                         (["--run", "-q", "Meta.lean"], None)):
        result = compare(args)
        r = next(r for r in rows() if r["args"] == args)
        assert r["input_kind"] == "unknown" and r["artifacts"] == []
        assert all(r[key] is None for key in ("source", "source_before", "source_after", "module_hint", "setup", "setup_fingerprint"))
        if output:
            assert result.returncode == 0 and (work / output).stat().st_size > 0
        evidence.append({"unsupported_case": args, "actual_status": result.returncode, "metadata_absent": True})
    return evidence


def metadata_reuse_controls(work, observer):
    """Actual producer/query counts using owned native constant-metadata images.

    This fixture obeys the native query-stability contract; its append-only log
    observes actual argv. It is not evidence that arbitrary ELF output is stable.
    """
    from concurrent.futures import ThreadPoolExecutor
    from overlay import create

    root = work / "metadata-reuse"
    (root / "native/bin").mkdir(parents=True)
    real = root / "native/bin/lean"
    log = root / "argv.jsonl"
    src = root / "compiler.c"
    source = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <signal.h>
#ifndef LABEL
#define LABEL "one"
#endif
int main(int argc, char **argv) {
    const char *log = getenv("METADATA_QUERY_LOG");
    if (log) { FILE *f = fopen(log, "a"); if (!f) return 91;
        for (int i = 1; i < argc; ++i) fprintf(f, "%s%s", i == 1 ? "" : "\t", argv[i]);
        fprintf(f, "\n"); fclose(f); }
    if (argc == 2 && !strcmp(argv[1], "--print-prefix")) {
        char p[4096]; ssize_t n = readlink("/proc/self/exe", p, sizeof(p)-1);
        if (n < 0) return 92; p[n] = 0;
        *strrchr(p, '/') = 0; *strrchr(p, '/') = 0; puts(p); return 0;
    }
    if (argc == 2 && !strcmp(argv[1], "--version")) {
        puts("Lean (version fixture-" LABEL ", commit 0123456789abcdef0123456789abcdef01234567, Release)"); return 0;
    }
    if (argc == 2 && !strcmp(argv[1], "--githash")) {
        puts("0123456789abcdef0123456789abcdef01234567"); return 0;
    }
    if (argc == 2 && !strcmp(argv[1], "--signal")) { raise(SIGTERM); return 93; }
    fputs("owned compiler stderr\n", stderr); puts(LABEL); return 7;
}
'''
    src.write_text(source)
    subprocess.run(["cc", "-O2", str(src), "-o", str(real)], check=True, capture_output=True)
    original = real.read_bytes()
    env = dict(os.environ, METADATA_QUERY_LOG=str(log))
    env.pop("HEAVY_BUDGET_DIR", None)
    env.pop("HEAVY_OBSERVE_DIR", None)
    overlay = create(root / "overlay", real, observer)
    shim = overlay / "bin/lean"
    prepared = overlay / "compiler-metadata"
    saved = prepared.read_bytes()
    assert prepared.stat().st_mode & 0o222 == 0
    evidence = []
    variable = {"child_pid", "start_monotonic_ns", "end_monotonic_ns", "wall_ns",
                "user_us", "system_us", "peak_rss_kib", "measured_cpu_us", "measured_peak_rss_kib"}

    def invoke(args, expected_queries):
        before = set((overlay / "records").glob("*.json"))
        log.write_text("")
        ordinary = subprocess.run([str(real), *args], env=env, capture_output=True, timeout=5)
        log.write_text("")
        observed = subprocess.run([str(shim), *args], env=env, capture_output=True, timeout=5)
        calls = log.read_text().splitlines()
        assert calls == expected_queries + ["\t".join(args)], calls
        assert (observed.returncode, observed.stdout, observed.stderr) == (
            ordinary.returncode, ordinary.stdout, ordinary.stderr), (ordinary, observed)
        added = set((overlay / "records").glob("*.json")) - before
        assert len(added) == 1
        row = json.loads(added.pop().read_text())
        assert row["args"] == args and row["shell_code"] == (128 - observed.returncode if observed.returncode < 0 else observed.returncode)
        evidence.append(dict(args=args, status=observed.returncode, calls=calls, record=row))
        return {k: v for k, v in row.items() if k not in variable}

    args = ["Missing.lean", "-o", "requested.olean", "--setup", "missing-setup.json"]
    reused = invoke(args, [])
    prepared.unlink()
    uncached = invoke(args, ["--version", "--githash"])
    assert reused == uncached, (reused, uncached)
    prepared.write_bytes(saved)
    for query in ("--version", "--githash"):
        invoke([query], [])  # actual query argv is still executed exactly once
    invoke(["--signal"], [])
    # Valid compiler argv never selects the setup-only basename entry.
    invoke(["--heavy-prepare-compiler-metadata", "x", "y"], [])
    # Well-formed version corruption, rather than merely a parse failure.
    prepared.write_bytes(saved.replace(b"fixture-one", b"fixture-bad"))
    invoke(args, ["--version", "--githash"])
    for corrupt in (b"\xff", b"partial\n", saved + b"trailing", saved.replace(b"\n", b"\r\n")):
        prepared.write_bytes(corrupt)
        invoke(args, ["--version", "--githash"])
    prepared.write_bytes(saved)
    # The executable still runs when its full image changes without changing
    # its path/size timestamp observations into a supplied validity verdict.
    real.write_bytes(original + b"changed image")
    invoke(args, ["--version", "--githash"])
    # Replace at the same pathname, preserving mtime, with different metadata.
    replacement = root / "replacement"
    subprocess.run(["cc", "-O2", '-DLABEL="two"', str(src), "-o", str(replacement)],
                   check=True, capture_output=True)
    info = real.stat()
    os.utime(replacement, ns=(info.st_atime_ns, info.st_mtime_ns))
    assert replacement.stat().st_size == len(original)
    replacement.replace(real)
    changed = invoke(args, ["--version", "--githash"])
    assert "fixture-two" in changed["compiler_version"]
    real.write_bytes(original)
    moved = real.with_name("missing-image")
    real.rename(moved)
    p = subprocess.run([str(shim), "--version"], env=env, capture_output=True, timeout=5)
    assert p.returncode == 127 and b"exec failed (errno 2)" in p.stderr
    missing = max((overlay / "records").glob("*.json"), key=lambda p: p.stat().st_mtime_ns)
    missing = json.loads(missing.read_text())
    assert missing["compiler_fingerprint"] is None and missing["compiler_version"] is None
    assert missing["compiler_githash"] is None and missing["exec_errno"] == 2
    moved.rename(real)
    evidence.append(dict(missing_image=True, physical_status=p.returncode, record=missing))
    # The same bytes at a different canonical compiler path do not reuse.
    copy = root / "native/bin/copy"
    copy.write_bytes(original); copy.chmod(0o755)
    (overlay / "real-lean.path").write_text(str(copy) + "\n")
    invoke(args, ["--version", "--githash"])
    (overlay / "real-lean.path").write_text(str(real) + "\n")
    prepared.chmod(0o444)
    log.write_text("")
    before = set((overlay / "records").glob("*.json"))
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(lambda _: subprocess.run([str(shim), "--version"],
            env=env, capture_output=True, timeout=5), range(8)))
    assert all(p.returncode == 0 and not p.stderr for p in results)
    assert log.read_text().splitlines() == ["--version"] * 8
    assert len(set((overlay / "records").glob("*.json")) - before) == 8
    assert prepared.read_bytes() == saved and prepared.stat().st_mode & 0o222 == 0
    evidence.append(dict(concurrent_readers=8, actual_calls=8, metadata_queries=0, immutable=True))
    # Scripts can return arbitrary environment-dependent query output. They
    # never enter the prepared domain, even when they print Lean-shaped text.
    script = root / "script/bin/lean"
    script.parent.mkdir(parents=True)
    script.write_text('#!/bin/sh\ncase "$1" in\n--print-prefix) dirname "$(dirname "$0")";;\n'
        '--version) echo "${VARIABLE_VERSION:-script-version}";;\n--githash) exit 9;;\n*) exit 7;;\nesac\n')
    script.chmod(0o755)
    unsupported = create(root / "unsupported", script, observer)
    assert not (unsupported / "compiler-metadata").exists()
    for version in ("first", "second"):
        p = subprocess.run([str(unsupported / "bin/lean"), "X.lean"],
            env={**env, "VARIABLE_VERSION": version}, capture_output=True, timeout=5)
        assert p.returncode == 7 and not p.stderr
    rows = [json.loads(p.read_text()) for p in (unsupported / "records").glob("*.json")]
    assert {r["compiler_version"] for r in rows} == {"first", "second"}
    assert all(r["compiler_githash"] is None for r in rows)
    evidence.append(dict(unsupported_script=True, versions=["first", "second"], failed_githash=None))
    # A four-byte format probe must not allocate a list for the full image.
    # Finite Linux wait4 regression only: these peaks are not private memory
    # or predictions. Compare two fresh owned helpers with generous slack.
    helper = root / ".prepare-compiler-metadata"
    helper.write_bytes(observer.read_bytes()); helper.chmod(0o700)
    peaks = []
    for label, size in (("small", len(original)), ("padded", 2097152)):
        image = root / (label + "-image")
        image.write_bytes(original + bytes(size - len(original))); image.chmod(0o700)
        output = root / (label + "-metadata")
        child = subprocess.Popen([str(helper), str(image), str(output)], env=env,
                                 stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        _, status, usage = os.wait4(child.pid, 0)
        child.returncode = os.waitstatus_to_exitcode(status)
        assert child.returncode == 0 and output.is_file()
        peaks.append(usage.ru_maxrss)
    assert peaks[1] - peaks[0] < 32768, peaks
    evidence.append(dict(prefix_probe_image_bytes=2097152, helper_peaks_kib=peaks))
    return evidence
