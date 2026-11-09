"""Heavy fixture adapter over the existing nonce/pidfd/subreaper runner.

No numeric-PID/group escalation: only independently pinned owned handles.
Signals request cancellation; they never interrupt the runner's cleanup. Nested
runners retain ancestor ownership markers, including across separate sessions.
"""
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess

ROOT = Path(__file__).resolve().parents[2]
_spec = importlib.util.spec_from_file_location('heavy_build_owned', ROOT / 'scripts/heavy_build_test.py')
_build = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_build)
_heavy = _build.load(ROOT / 'scripts/heavy')
OwnedRun = _build.OwnedRun


def run(command, *, directory, label, cwd=None, env=None, timeout=12, grace=2,
        check=False, ready=None, action=None):
    directory = Path(directory)
    owner = OwnedRun(_heavy, directory, label)
    cancellations, previous = [], {}
    def cancel(sig, _frame):
        cancellations.append(sig)
        if owner.cancelled is None:
            owner.cancelled = sig
    for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        previous[sig] = signal.getsignal(sig)
        if previous[sig] != signal.SIG_IGN:
            signal.signal(sig, cancel)
    try:
        child_env = dict(os.environ if env is None else env)
        # Caller-supplied minimal environments still retain only the ancestor
        # ownership markers, not unrelated caller settings.
        for key, value in os.environ.items():
            if key.startswith('HEAVY_TEST_OWNED_'):
                child_env.setdefault(key, value)
        row, out, err = owner.execute(command, cwd=cwd or Path.cwd(), env=child_env,
            timeout=timeout, grace=grace, ready=ready, action=action, input_data=b'')
        row['cancel_signals'] = cancellations
        (directory / (label + '.json')).write_text(json.dumps(row, indent=2) + '\n')
        if row['cleanup']['outcome'] != 'complete':
            raise RuntimeError(f"owned cleanup unestablished; retain {directory / (label + '.json')}")
        if cancellations:
            raise SystemExit(128 + cancellations[0])
        if row['failure'] is not None:
            if row['failure'].startswith('TimeoutError('):
                raise subprocess.TimeoutExpired(command, timeout, output=out, stderr=err)
            raise RuntimeError(f"owned command failed: {row['failure']}; {directory / (label + '.json')}")
        result = subprocess.CompletedProcess(command, row['physical_status'], out, err)
        if check:
            try:
                result.check_returncode()
            except subprocess.CalledProcessError as error:
                error.add_note(f"owned receipt: {directory / (label + '.json')}\n{err.decode(errors='replace')}")
                raise
        return result
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)
