#!/usr/bin/env python3
"""Source-bound integration checks for the in-place native wrapper."""
import argparse
import json
import os
import re
import resource
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

from native_test_process import NativeTimeout, cleanup, initialize, run


def fault_context_matches(report):
    """Compare real stopped code/PC/registers with the captured thread stack."""
    fault = report["faults"][0]
    context = fault["context"]
    thread = context["thread"]
    assert thread["global_num"] > 0 and thread["ptid"][0] == report["original_pid"], context
    assert context["pc"] > 0 and context["architecture"], context
    instructions = context["instructions"]
    assert 1 <= len(instructions) <= 3 and instructions[0]["addr"] == context["pc"], context
    for i, instruction in enumerate(instructions):
        assert instruction["length"] > 0 and 0 < len(instruction["asm"]) <= 256, context
        if i:
            previous = instructions[i - 1]
            assert instruction["addr"] == previous["addr"] + previous["length"], context
    name = context["architecture"]
    if name.startswith("i386:x86-64"):
        expected = {"rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp"} | {f"r{i}" for i in range(8, 16)}
    elif name == "i386":
        expected = {"eax", "ebx", "ecx", "edx", "esi", "edi", "ebp", "esp"}
    elif name.startswith("aarch64"):
        expected = {f"x{i}" for i in range(31)} | {"sp"}
    else:
        expected = set()
        assert context["unavailable"]["registers"], context
    assert set(context["registers"]) == expected, context
    assert all(type(value) is int for value in context["registers"].values()), context
    if sys.platform == "linux":
        # GDB's Linux thread header ties these facts to the actual fault
        # LWP, not another thread printed by `thread apply all`.
        stack = re.search(rf"^Thread {thread['global_num']} [^\n]*\(LWP {thread['ptid'][1]}\)[^\n]*\n(#0[^\n]+)",
                          fault["backtrace"], re.MULTILINE)
        assert stack, context
        # A fully symbolized source frame may omit its address in `bt`.
        address = re.match(r"#0\s+(0x[0-9a-fA-F]+)\b", stack[1])
        if address:
            assert int(address[1], 16) == context["pc"], context
    assert all("context" not in later for later in report["faults"][1:]), report


def core(args, driver, wrapper, destination, debugger, protected, unprotected):
    # The real harness must fail when its required tool is absent, rather
    # than silently omitting native-frame assertions.
    with tempfile.TemporaryDirectory(prefix="fren-no-debugger-") as empty:
        missing = run([sys.executable, str(Path(__file__).resolve()), "--driver", driver],
                      env=dict(os.environ, PATH=empty))
    assert missing.returncode == 125 and not missing.stdout, missing
    assert "requires GDB in PATH" in missing.stderr and "skipped" not in missing.stderr, missing
    if destination:
        (destination / "missing-environment.json").write_text(json.dumps({
            "status": missing.returncode, "stdout": missing.stdout, "stderr": missing.stderr,
            "cleanup": missing.cleanup}, indent=2) + "\n")
    for probe, sig in [("nativeDiagnosticProbe", 6), ("ownSpecProgressProbe", 8)]:
        refused = run([driver, "--job", probe, "crash"], env=unprotected)
        assert refused.returncode != 0 and refused.returncode != -sig, refused
        assert "requires FREN_NATIVE_CORELESS=1" in refused.stderr, refused
    plain = run([driver, "--job", "nativeDiagnosticProbe", "pass"], env=unprotected)
    assert plain.returncode == 0 and plain.stdout.strip() == "[]" and not plain.stderr, plain
    with tempfile.TemporaryDirectory(prefix="fren-native-raw-") as directory:
        journal = Path(directory) / "progress"
        journal.touch()
        start = time.monotonic()
        try:
            crash = run([driver, "--job", "nativeDiagnosticProbe", "crash"],
                        env=dict(protected, FREN_ENUM_PROGRESS=str(journal)))
        except NativeTimeout as error:
            error.receipt["context"] = journal.read_text()
            raise NativeTimeout(error.receipt) from error
        context = journal.read_text()
        assert crash.returncode == -6 and not crash.stdout and not crash.stderr, crash
        assert "first" in context, context
        if sys.platform == "linux":
            assert '["native-core-policy","rlimit=0","dumpable=0"]' in context, context
        if destination:
            (destination / "raw-abort.json").write_text(json.dumps({
                "status": crash.returncode, "stdout": crash.stdout, "stderr": crash.stderr,
                "seconds": time.monotonic() - start, "context": context,
                "cleanup": crash.cleanup}, indent=2) + "\n")


def wait(args, driver, wrapper, destination, debugger, protected, unprotected):
    # Exercise the source-bound terminal-wait helper inside real GDB,
    # including a nonzero exit and a live child that must remain a failure.
    # This does not rely on winning the zombie-leader race to cover it.
    with tempfile.TemporaryDirectory(prefix="fren-native-wait-") as directory:
        root = Path(directory)
        helper = str(Path(__file__).with_name("native_diag_gdb.py").resolve())
        script = root / "wait.py"
        script.write_text("import runpy,subprocess,sys,time,json\nfrom pathlib import Path\n" +
                          "ns=runpy.run_path(" + repr(helper) + ")\n" +
                          "driver=" + repr(driver) + "\npython=" + repr(sys.executable) +
                          "\nreceipt_path=" + repr(str(root / "wait-receipt.json")) + "\n" + r"""
# The one bootstrap original belongs to the production observer. Do not
# overwrite its terminal receipt with the utility test children's statuses.
assert ns["state"]["exit_code"] == 0 and not ns["state"]["error"], ns["state"]
production_root = ns["root"]
globals_ = ns["reap_terminal"].__globals__
production_state = globals_["state"]
utility_root = production_root / "wait-controls"
utility_root.mkdir()
globals_["root"] = utility_root
globals_["state"] = {"exit_code": None, "terminal_signal": None}
rows = []
for command, expected in [([python, "-c", "raise SystemExit(23)"], 23),
                          ([driver, "--job", "nativeDiagnosticProbe", "crash"], -6),
                          ([python, "-c", "import time; time.sleep(60)"], None)]:
    child = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    globals_["state"].update(exit_code=None, terminal_signal=None)
    start = time.monotonic()
    try:
        try:
            ns["reap_terminal"](child.pid)
        except RuntimeError as error:
            assert expected is None and "did not complete" in str(error), str(error)
            rows.append({"timed_out": True, "pid": child.pid, "seconds": time.monotonic() - start})
        else:
            state = globals_["state"]
            actual = -state["terminal_signal"] if state["terminal_signal"] else state["exit_code"]
            assert actual == expected and expected is not None, state
            assert state["terminal_status_source"] == "waitpid", state
            child.returncode = actual
            rows.append({"status": actual, "pid": child.pid, "source": state["terminal_status_source"],
                         "raw_wait": state["terminal_wait"]})
    finally:
        if child.returncode is None:
            child.kill()
        child.communicate(timeout=2)
    assert child.returncode == (expected if expected is not None else -9), child.returncode
Path(receipt_path).write_text(json.dumps(rows))
globals_["root"] = production_root
globals_["state"] = production_state
""")
        # Use the production observer for this GDB call too: a bootstrap
        # or shutdown stall must not bypass it and consume the outer 60s.
        tool = root / "wait-gdb"
        tool.write_text("#!" + sys.executable + "\nimport os,sys\na=sys.argv[1:]\n" +
            "a[a.index('-x')+1]=" + repr(str(script)) + "\nos.execv(" + repr(debugger) +
            ", [" + repr(debugger) + "]+a)\n")
        tool.chmod(0o755)
        report_file = root / "report.json"
        checked = run([sys.executable, wrapper, "--report", str(report_file), "--debugger", str(tool),
                       "--", driver, "--job", "nativeDiagnosticProbe", "pass"], env=protected)
        original = json.loads(report_file.read_text())
        if destination:
            shutil.copyfile(report_file, destination / "terminal-wait-observer.json")
        assert checked.returncode == 0 and (root / "wait-receipt.json").exists(), (checked, original)
        assert original["original_exit"] == 0 and original["debugger_exit"] == 0, original
        rows = json.loads((root / "wait-receipt.json").read_text())
        assert all(row["pid"] != original["original_pid"] for row in rows), (rows, original)
        if destination:
            shutil.copyfile(root / "wait-receipt.json", destination / "terminal-wait.json")


def own(args, driver, wrapper, destination, debugger, protected, unprotected):
    # The production initial-check boundary serializes its actual verdict
    # and output. Exercise both caller decoders: valid JSON must not hide
    # a missing debugger's 125, and a real native crash must retain frames.
    with tempfile.TemporaryDirectory(prefix="fren-own-native-") as directory:
        root = Path(directory)
        empty = root / "tools"
        empty.mkdir()
        (empty / "python3").symlink_to(sys.executable)
        live = root / "live.jsonl"
        live.touch()
        cohort = [["ownSpec"], ["nativeDiagnosticSibling"]]
        for name, command, absent in [
                ("initial-pass", ["--native-initial-parent", "pass"], False),
                ("initial-crash", ["--native-initial-parent", "crash"], False),
                ("initial-stderr", ["--native-initial-parent", "stderr"], False),
                ("persistent-pass", ["--native-persistent-parent"], False),
                ("initial-missing", ["--native-initial-parent", "pass"], True),
                ("persistent-missing", ["--native-persistent-parent"], True)]:
            journal = root / (name + ".jsonl")
            journal.touch()
            report_file = root / (name + ".json")
            env = dict(protected, FREN_DIAG_OWN_SPEC_INITIAL="1",
                       FREN_OWN_DIAG_CONTEXT=json.dumps([cohort, 2]),
                       FREN_NATIVE_LIVE_FILE=str(live),
                       FREN_OWN_SPEC_PROGRESS=str(journal),
                       FREN_ENUM_DIAG_RECEIPT=str(report_file))
            if absent:
                env["PATH"] = str(empty)
            child = run([driver, *command], env=env)
            report = json.loads(report_file.read_text())
            if destination:
                shutil.copyfile(report_file, destination / (name + ".json"))
                shutil.copyfile(journal, destination / (name + ".jsonl"))
                (destination / (name + "-caller.json")).write_text(json.dumps({
                    "status": child.returncode, "stdout": child.stdout,
                    "stderr": child.stderr, "cleanup": child.cleanup}, indent=2) + "\n")
            assert report["cohort"] == cohort and report["workers"] == 2, report
            assert report["progress_env"] == "FREN_OWN_SPEC_PROGRESS", report
            assert report["command"][0] == driver, report
            if absent:
                assert child.returncode != 0, child
                assert report["original_exit"] == 0 and report["status"] == 125, report
                assert report["debugger_status"] == "missing", report
                assert "125" in child.stderr, child
            elif name == "initial-crash":
                assert child.returncode != 0, child
                assert report["original_exit"] == 134 and report["original_signal"] == 6, report
                assert report["debugger_exit"] == 0 and report["debugger_status"] == "captured", report
                assert report["original_pid"] > 0 and not report["terminated_by_debugger"], report
                assert "fren_test_raise_abrt" in report["faults"][0]["backtrace"], report
                assert "si_signo" in report["faults"][0]["siginfo"], report
                assert "first" in journal.read_text(), report
            else:
                assert child.returncode == 0, child
                if name == "initial-stderr":
                    assert child.stderr == "initial child stderr must survive\n", child
                else:
                    assert not child.stderr, child
                assert json.loads(child.stdout)[0] == "0", child
                assert report["original_exit"] == 0 and not report["faults"], report
            if name.startswith("initial"):
                assert "initial-input" in journal.read_text(), journal.read_text()
            else:
                assert "persistent-invocation" in journal.read_text(), journal.read_text()
                assert report["command"][1:6] == ["--job", "persistentRun", "check", "--jobs", "4"], report


def wrapper_checks(args, driver, wrapper, destination, debugger, protected, unprotected):
    plain = run([driver, "--job", "nativeDiagnosticProbe", "pass"], env=unprotected)
    # An actual sibling stays alive while the controlled child crashes.
    # The wrapper must target/reap only its own inferior, not this cohort.
    sibling = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
    try:
        with tempfile.TemporaryDirectory(prefix="fren-native-diag-test-") as directory:
            if sys.platform == "linux" and os.geteuid() == 0:
                # Heavy's offline namespace maps its caller to UID 0.
                # Exercise ordinary non-root proc ownership even there;
                # exec drops the nested namespace's capabilities.
                unshare = shutil.which("unshare")
                assert unshare, "root native wrapper regression requires unshare"
                nonroot = Path(directory) / "nonroot-gdb"
                prefix = [unshare, "--user", "--map-user=1000", "--map-group=1000", "--", debugger]
                nonroot.write_text("#!" + sys.executable + "\nimport os,sys\nprefix=" + repr(prefix) +
                                   "\nos.execv(prefix[0],prefix+sys.argv[1:])\n")
                nonroot.chmod(0o755)
                debugger = str(nonroot)
            cases = [("pass", "fren-deliberately-missing-debugger", 125),
                     ("pass", debugger, 0), ("crash", debugger, 134)]
            for i, (mode, tool, expected) in enumerate(cases):
                cohort = [["nativeDiagnosticProbe", mode], ["nativeDiagnosticSibling"]]
                report_file = Path(directory) / f"report-{i}.json"
                command = [sys.executable, wrapper, "--report", str(report_file),
                           "--cohort", json.dumps(cohort), "--workers", "2", "--debugger", tool,
                           "--", driver, "--job", "nativeDiagnosticProbe", mode]
                child = run(command, peers=(sibling.pid,))
                report = json.loads(report_file.read_text())
                if args.receipts:
                    (destination / f"case-{i}.json").write_text(json.dumps(report, indent=2) + "\n")
                assert child.returncode == expected, (command, child.returncode, child.stderr)
                assert report["cohort"] == cohort and report["workers"] == 2, report
                if tool != "fren-deliberately-missing-debugger":
                    assert report["terminal_status_source"] in ["gdb", "waitpid"], report
                if tool != "fren-deliberately-missing-debugger" and sys.platform == "linux":
                    assert report["debugger_core_policy"] == {"rlimit_core": [0, 0], "dumpable": 0}, report
                    startup = report["debugger_state"]["startup"]
                    assert startup["pid"] == report["original_pid"], startup
                    assert startup["ptid"][1] == startup["pid"], startup
                    assert startup["exe"] == os.path.realpath(driver) and startup["pc"] != 0, startup
                    assert startup["debugger_uid"] != 0, startup
                    assert startup["debugger_capabilities"] == [
                        "CapPrm:\t0000000000000000", "CapEff:\t0000000000000000"], startup
                    assert startup["debugger_dumpable_before"] == 1, startup
                    assert startup["debugger_dumpable_after"] == 0, startup
                assert '["phase","controlled-check"]' in report["context"], report
                assert '["method","solver"]' in report["context"], report
                assert "own_spec_progress.fren" in report["context"], report
                assert '["diagnostic-env","0","1"]' in report["context"], report
                if sys.platform == "linux":
                    assert '["native-core-policy","rlimit=0","dumpable=0"]' in report["context"], report
                assert sibling.poll() is None, "diagnostics terminated the sibling workload"
                assert "captured output must not escape" not in child.stdout, child.stdout
                if tool == "fren-deliberately-missing-debugger":
                    assert report["debugger_status"] == "missing", report
                    assert report["original_exit"] == 0, report
                    assert child.stdout.strip() == "[]", child.stdout
                    assert "unavailable" in child.stderr, child.stderr
                elif mode == "pass":
                    assert report["original_exit"] == 0 and report["original_signal"] is None, report
                    assert report["debugger_exit"] == 0 and not report["faults"], report
                    assert report["debugger_status"] == "captured", report
                    assert child.stdout == plain.stdout and not child.stderr, child
                else:
                    assert report["original_signal"] == 6, report
                    assert report["original_exit"] == 134 and not report["terminated_by_debugger"], report
                    assert report["debugger_status"] == "captured" and not report["error"], report
                    assert report["debugger_exit"] == 0, report
                    assert report["faults"][0]["signal"] == "SIGABRT", report
                    assert "#0" in report["faults"][0]["backtrace"], report
                    assert "si_signo" in report["faults"][0]["siginfo"], report
                    fault_context_matches(report)
                    assert "first" in report["context"] and not child.stdout, report
                    assert "SIGABRT" in child.stderr and "backtrace" in child.stderr, child.stderr
                print(json.dumps({"mode": mode, "debugger": tool, "status": child.returncode,
                                  "original_exit": report["original_exit"],
                                  "original_signal": report["original_signal"],
                                  "debugger_exit": report["debugger_exit"]}))
            # A handler that returns must not erase a recorded fault,
            # even when this same original child later exits zero.
            report_file = Path(directory) / "handled.json"
            handled = "import os,signal; signal.signal(signal.SIGSEGV,lambda *_:None); os.kill(os.getpid(),signal.SIGSEGV)"
            child = run([sys.executable, wrapper, "--report", str(report_file),
                         "--debugger", debugger,
                         "--", sys.executable, "-c", handled], peers=(sibling.pid,))
            report = json.loads(report_file.read_text())
            if args.receipts:
                (Path(args.receipts) / "handled.json").write_text(json.dumps(report, indent=2) + "\n")
            assert child.returncode == 139 and report["original_exit"] == 0, report
            assert report["original_signal"] is None and report["fault_signal"] == 11, report
            assert report["debugger_exit"] == 0 and report["debugger_status"] == "captured", report
            assert report["terminal_status_source"] in ["gdb", "waitpid"], report
            assert not report["terminated_by_debugger"] and sibling.poll() is None, report
            fault_context_matches(report)
            # A hung leader and its pipe-holding descendant must be killed
            # and reaped without touching the deliberately live peer.
            hanging = "import time; time.sleep(60)"
            if sys.platform == "linux":
                # Linux's subreaper additionally owns the orphaned pipe
                # holder; other platforms exercise the direct child.
                hanging = "import os,time; p=os.fork(); print(os.getpid(),p,flush=True); time.sleep(60)"
            try:
                run([sys.executable, "-c", hanging], timeout=1, peers=(sibling.pid,))
                raise AssertionError("the controlled hang unexpectedly completed")
            except NativeTimeout as error:
                assert error.receipt["timed_out"] and not error.receipt["remaining"], error.receipt
                assert not error.receipt["errors"], error.receipt
                assert error.receipt["child_returncode"] == -9, error.receipt
                if sys.platform == "linux":
                    assert error.receipt["reaped"], error.receipt
                assert sibling.poll() is None, error.receipt
                if args.receipts:
                    (Path(args.receipts) / "timeout.json").write_text(json.dumps(error.receipt, indent=2) + "\n")
    finally:
        sibling.terminate()
        try:
            sibling.wait(timeout=2)
        except subprocess.TimeoutExpired:
            receipt = cleanup(sibling, ())
            raise AssertionError(f"native test peer did not terminate: {receipt}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--driver", required=True)
    parser.add_argument("--receipts")
    parser.add_argument("--group", choices=["core", "wait", "own", "wrapper"])
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    driver = str(Path(args.driver).resolve())
    wrapper = str(Path(__file__).with_name("native_diagnostic.py"))
    destination = Path(args.receipts) if args.receipts else None
    if destination:
        destination.mkdir(parents=True, exist_ok=True)
    debugger = shutil.which("gdb")
    if not debugger:
        print("native diagnostic harness requires GDB in PATH", file=sys.stderr)
        return 125
    initialize()
    protected = dict(os.environ, FREN_NATIVE_CORELESS="1")
    unprotected = dict(os.environ)
    unprotected.pop("FREN_NATIVE_CORELESS", None)
    groups = {"core": core, "wait": wait, "own": own, "wrapper": wrapper_checks}
    for name, check in groups.items():
        if args.group is None or name == args.group:
            check(args, driver, wrapper, destination, debugger, protected, unprotected)
    return 0


if __name__ == "__main__":
    sys.exit(main())
