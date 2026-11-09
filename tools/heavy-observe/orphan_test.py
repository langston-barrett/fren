"""Kernel-checked exited-orphan and foreign-child controls for OwnedRun.

The fixture knows exact fork/Popen children independently of the runner. It
never accepts the runner's own empty remaining list as proof of reaping.
"""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

from owned_test import run as owned_run


def state(pid):
    raw = Path(f'/proc/{pid}/stat').read_text()
    fields = raw[raw.rfind(')') + 2:].split()
    return dict(pid=pid, state=fields[0], ppid=int(fields[1]), start=int(fields[19]))


def children():
    # Independent of OwnedRun's marker scan, handles and completion fields.
    result = set()
    for task in Path('/proc/self/task').iterdir():
        result.update(map(int, (task / 'children').read_text().split()))
    return result


def controls(work, env):
    worker = work / 'early-orphan.py'
    worker.write_text(r'''
import json,os,sys,time
from pathlib import Path
pid=os.fork()
if pid==0: os._exit(17)
# WNOWAIT establishes an already-exited exact fork child without consuming it.
observed=os.waitid(os.P_PID,pid,os.WEXITED|os.WNOWAIT)
raw=Path(f'/proc/{pid}/stat').read_text();fields=raw[raw.rfind(')')+2:].split()
Path(sys.argv[1]).write_text(json.dumps({'pid':pid,'start':int(fields[19]),'wait_pid':observed.si_pid,'exit_status':observed.si_status}))
print('orphan-parent stdout',flush=True)
print('orphan-parent stderr',file=sys.stderr,flush=True)
time.sleep(.1)
''')
    marker = work / 'early-orphan.ready'
    orphan = None
    orphan_reaped = False
    result = {}
    try:
        try:
            owned_run([sys.executable, '-I', str(worker), str(marker)], directory=work,
                      label='early-orphan', env=env, timeout=2, grace=.1)
        except RuntimeError as error:
            result['adapter_error'] = str(error)
            assert 'owned cleanup unestablished' in str(error), error
        else:
            raise AssertionError('unattributed exited child was certified complete')
        orphan = json.loads(marker.read_text())
        observed = state(orphan['pid'])
        assert orphan['wait_pid'] == orphan['pid'] and orphan['exit_status'] == 17
        assert observed['start'] == orphan['start'] and observed['state'] == 'Z'
        assert observed['ppid'] == os.getpid() and orphan['pid'] in children(), observed
        receipt = json.loads((work / 'early-orphan.json').read_text())
        assert receipt['physical_status'] == 0 and receipt['physical_status_known']
        assert receipt['cleanup']['outcome'] == 'unknown' and not receipt['product_success']
        assert any(r['pid'] == orphan['pid'] and r['start'] == orphan['start']
                   for r in receipt['cleanup']['unattributed_children']), receipt
        assert (work / 'early-orphan.stdout').read_bytes() == b'orphan-parent stdout\n'
        assert (work / 'early-orphan.stderr').read_bytes() == b'orphan-parent stderr\n'
        # Only this fixture has independent provenance for that exact fork.
        # Reap it explicitly; no blanket wait and no signal to an unknown child.
        reaped = os.waitpid(orphan['pid'], os.WNOHANG)
        assert reaped == (orphan['pid'], 17 << 8), reaped
        assert orphan['pid'] not in children()
        result.update(orphan=orphan, kernel_before_reap=observed,
                      exact_fixture_reap=list(reaped), receipt=receipt)
        orphan_reaped = True
    finally:
        if not orphan_reaped and orphan is None and marker.exists():
            orphan = json.loads(marker.read_text())
        if not orphan_reaped and orphan is not None:
            try:
                remaining = state(orphan['pid'])
                if remaining['ppid'] == os.getpid() and remaining['start'] == orphan['start'] and remaining['state'] == 'Z':
                    os.waitpid(orphan['pid'], os.WNOHANG)
            except (FileNotFoundError, ProcessLookupError, ChildProcessError):
                pass

    # Baseline foreign children must not be consumed or signalled. One is live;
    # one is a zombie with no usable environment, both created before the run.
    live = subprocess.Popen([sys.executable, '-I', '-c', 'import time; time.sleep(10)'])
    exited, live_fd = None, None
    try:
        live_fd = os.pidfd_open(live.pid)
        exited = subprocess.Popen([sys.executable, '-I', '-c', 'import os; os._exit(23)'])
        deadline = time.monotonic() + 2
        while state(exited.pid)['state'] != 'Z' and time.monotonic() < deadline:
            time.sleep(.01)
        before = state(exited.pid); live_before = state(live.pid)
        assert before['state'] == 'Z' and {live.pid, exited.pid} <= children()
        p = owned_run([sys.executable, '-I', '-c',
                       'import sys; print("status stdout"); print("status stderr",file=sys.stderr); sys.exit(7)'],
                      directory=work, label='foreign-preservation', env=env, timeout=2, grace=.1)
        assert (p.returncode, p.stdout, p.stderr) == (7, b'status stdout\n', b'status stderr\n')
        assert live.poll() is None and state(live.pid)['start'] == live_before['start']
        after = state(exited.pid)
        assert after == before and exited.pid in children(), (before, after)
        reaped = os.waitpid(exited.pid, os.WNOHANG)
        assert reaped == (exited.pid, 23 << 8), reaped
        exited.returncode = 23
        receipt = json.loads((work / 'foreign-preservation.json').read_text())
        assert receipt['cleanup']['outcome'] == 'complete'
        assert [before['pid'], before['start']] in receipt['cleanup']['preexisting_children']
        result['foreign'] = dict(before=before, after=after, exact_fixture_reap=list(reaped),
                                 live_before=live_before, live_after=state(live.pid), receipt=receipt)
    finally:
        try:
            if exited is not None and exited.returncode is None:
                exited.wait(timeout=2)  # Exact Popen child; never another caller's.
        finally:
            # live is this fixture's exact, unreaped Popen child. Even a
            # pidfd-open failure must not skip its bounded cleanup.
            def stop(sig):
                try:
                    if live_fd is None:
                        live.send_signal(sig)
                    else:
                        signal.pidfd_send_signal(live_fd, sig)
                except ProcessLookupError:
                    pass
            try:
                stop(signal.SIGTERM)
                try:
                    live.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    stop(signal.SIGKILL)
                    live.wait(timeout=2)
            finally:
                if live_fd is not None:
                    os.close(live_fd)
    (work / 'orphan-result.json').write_text(json.dumps(result, indent=2) + '\n')
    return result
