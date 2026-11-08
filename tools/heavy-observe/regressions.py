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
