#!/usr/bin/env python3
"""Actual transport cancellation and cleanup controls, with owned processes."""
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
root = Path(__file__).resolve().parents[2]
helper = root / 'src/FrenOirToSmt/transport.py'
spec = importlib.util.spec_from_file_location('walking_smt_transport', helper)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
records = []
with tempfile.TemporaryDirectory(prefix='walking-smt-control-') as directory:
    ready = Path(directory) / 'pid'
    command = [sys.executable, '-c',
               'import os,sys,time;open(sys.argv[1],"w").write(str(os.getpid()));time.sleep(60)', str(ready)]
    request = dict(command=command, script='', wall_ms=2000, output_bytes=1024, input_bytes=1024)
    child = subprocess.Popen([sys.executable, str(helper)], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    solver_pid = None
    try:
        child.stdin.write(json.dumps(request).encode())
        child.stdin.close()
        until = time.monotonic() + 1
        while not ready.exists() and time.monotonic() < until:
            time.sleep(.005)
        assert ready.exists(), 'owned solver readiness failed'
        solver_pid = int(ready.read_text())
        child.send_signal(signal.SIGTERM)
        child.send_signal(signal.SIGTERM)
        child.wait(timeout=2)
        result = json.loads(child.stdout.read())
        assert result['kind'] == 'resource' and result['reason'] == 'transport cancelled', result
        assert result['exit_code'] == -signal.SIGKILL, result
        assert not Path(f'/proc/{solver_pid}').exists(), 'owned solver was not reaped'
        records.append(result)
    finally:
        if child.poll() is None:
            child.kill()
        child.wait()
        if solver_pid is not None:
            try:
                os.killpg(solver_pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
# Deliver real repeated signals at cleanup entry, without production test hooks.
original_killpg = mod.os.killpg
signal.signal(signal.SIGTERM, mod.request_cancel)
def cleanup_entry(pid, sig):
    os.kill(os.getpid(), signal.SIGTERM)
    os.kill(os.getpid(), signal.SIGTERM)
    original_killpg(pid, sig)
mod.os.killpg = cleanup_entry
try:
    result = mod.run(dict(command=[sys.executable, '-c', 'import time;time.sleep(60)'],
                          script='', wall_ms=50, output_bytes=1024, input_bytes=1024))
    assert result['kind'] == 'resource' and result['reason'] == 'transport cancelled', result
    assert result['exit_code'] == -signal.SIGKILL, result
    records.append(result)
finally:
    mod.os.killpg = original_killpg
if os.environ.get('FREN2_SMT_EVIDENCE_DIR'):
    path = Path(os.environ['FREN2_SMT_EVIDENCE_DIR'])
    path.mkdir(parents=True, exist_ok=True)
    (path / f'{os.getpid()}-cancellation.json').write_text(json.dumps(records, indent=2) + '\n')
print('owned repeated cancellation and cleanup-entry signals passed')
