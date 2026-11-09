#!/usr/bin/env python3
"""Actual transport ownership, cancellation and cleanup controls."""
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import threading
import time

sys.dont_write_bytecode = True
root = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('walking_smt_transport', root / 'src/FrenOirToSmt/transport.py')
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
signal.signal(signal.SIGCHLD, signal.SIG_DFL)
signal.signal(signal.SIGTERM, mod.request_cancel)
real_popen = subprocess.Popen
real_killpg = os.killpg
records = []
children = []
observations = []
cleanup_signals = False


def tracked_popen(*args, **kwargs):
    child = real_popen(*args, **kwargs)
    children.append(child)
    return child


def anchored_signal(pid, sig):
    # This is a kernel ownership test, not a /proc existence or status check.
    # It fails on the old successful-exit path that polled/reaped the leader.
    info = os.waitid(os.P_PID, pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
    assert any(c.pid == pid for c in children), 'not an owned direct child'
    observations.append(dict(pid=pid, signal=sig, leader_still_waitable=True,
                             leader_state='running' if info is None else 'exited'))
    if cleanup_signals:
        # Repeated actual cancellation at cleanup entry cannot release the
        # leader or interrupt the anchored group signal and following reap.
        os.kill(os.getpid(), signal.SIGTERM)
        os.kill(os.getpid(), signal.SIGTERM)
    real_killpg(pid, sig)


mod.subprocess.Popen = tracked_popen
mod.os.killpg = anchored_signal


def check(name, command, script='', wall_ms=100, expected_kind='finished', expected_code=0,
          expected_state='exited', at_cleanup=False, cancel_ready=None):
    global cleanup_signals
    mod.cancel_requested = False
    cleanup_signals = at_cleanup
    children.clear()
    observations.clear()
    cancel_errors = []
    sender = None
    if cancel_ready is not None:
        def cancel():
            until = time.monotonic() + 1
            while not cancel_ready.exists() and time.monotonic() < until:
                time.sleep(.005)
            if not cancel_ready.exists():
                cancel_errors.append('owned solver readiness failed')
                return
            os.kill(os.getpid(), signal.SIGTERM)
            os.kill(os.getpid(), signal.SIGTERM)
        sender = threading.Thread(target=cancel)
        sender.start()
    try:
        result = mod.run(dict(command=command, script=script, wall_ms=wall_ms,
                              output_bytes=1024, input_bytes=1024))
        if sender is not None:
            sender.join(timeout=2)
            assert not sender.is_alive() and not cancel_errors, cancel_errors
        assert result['kind'] == expected_kind and result['exit_code'] == expected_code, result
        if at_cleanup or cancel_ready is not None:
            assert result['reason'] == 'transport cancelled', result
        assert len(observations) == 1, observations
        assert observations[0]['leader_state'] == expected_state, observations
        # The production helper, not this harness, must perform the reap.
        try:
            os.waitid(os.P_PID, children[0].pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
        except ChildProcessError:
            pass
        else:
            raise AssertionError('production left the owned direct child waitable')
        records.append(dict(case=name, receipt=result, ownership_checks=list(observations)))
    finally:
        if sender is not None:
            sender.join(timeout=2)
        for child in children:
            # Failure cleanup is also conditional on an unreaped direct-child
            # anchor. Never signal the old solver PID after production reaped.
            try:
                os.waitid(os.P_PID, child.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
            except ChildProcessError:
                continue
            try:
                real_killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            child.wait()
        cleanup_signals = False


try:
    solver = root / '.lake/packages/cvc5/cvc5-Linux-x86_64-static/bin/cvc5'
    check('real-cvc5-normal-unsat', [str(solver), '--lang=smt2'],
          '(set-logic ALL)\n(assert false)\n(check-sat)\n', wall_ms=1000)
    assert records[-1]['receipt']['stdout'] == 'unsat\n'
    check('normal-nonzero', [sys.executable, '-c', 'print("unsat");raise SystemExit(7)'], expected_code=7, wall_ms=1000)
    check('closed-streams-normal-exit', [sys.executable, '-c',
          'import os,time;os.close(1);os.close(2);time.sleep(.02)'], wall_ms=500)
    with tempfile.TemporaryDirectory(prefix='walking-smt-control-') as directory:
        ready = Path(directory) / 'pid'
        command = [sys.executable, '-c',
                   'import os,sys,time;open(sys.argv[1],"w").write(str(os.getpid()));time.sleep(60)', str(ready)]
        check('repeated-running-cancellation', command, wall_ms=2000, expected_kind='resource',
              expected_code=-signal.SIGKILL, expected_state='running', cancel_ready=ready)
    check('repeated-cleanup-entry-cancellation', [sys.executable, '-c', 'import time;time.sleep(60)'],
          expected_kind='resource', expected_code=-signal.SIGKILL, expected_state='running', at_cleanup=True)
    check('exited-leader-with-pipe-holding-descendant', [sys.executable, '-c',
          'import subprocess,sys;subprocess.Popen([sys.executable,"-c","import time;time.sleep(60)"])'],
          expected_kind='resource', expected_state='exited', wall_ms=500)
    # An unexpected reaper must turn even an unsat response into an error,
    # without any remembered-group signal. Cancellation cannot mask the loss.
    real_observe = mod.observe_exit
    def release_anchor(child):
        info = real_observe(child)
        if info is not None:
            child.wait()  # Deliberate test-only loss, never production policy.
            mod.cancel_requested = True
        return real_observe(child)
    mod.cancel_requested = False
    children.clear()
    observations.clear()
    mod.observe_exit = release_anchor
    try:
        result = mod.run(dict(command=[sys.executable, '-c', 'print("unsat")'],
                              script='', wall_ms=1000, output_bytes=1024, input_bytes=1024))
        assert result['kind'] == 'error' and 'no longer waitable' in result['reason'], result
        assert result['stdout'] == 'unsat\n' and not observations, result
        records.append(dict(case='lost-anchor-no-signal', receipt=result, ownership_checks=[]))
    finally:
        mod.observe_exit = real_observe
finally:
    mod.subprocess.Popen = real_popen
    mod.os.killpg = real_killpg
if os.environ.get('FREN2_SMT_EVIDENCE_DIR'):
    path = Path(os.environ['FREN2_SMT_EVIDENCE_DIR'])
    path.mkdir(parents=True, exist_ok=True)
    (path / f'{os.getpid()}-ownership.json').write_text(json.dumps(records, indent=2) + '\n')
print('owned cleanup: six kernel waitability checks at group signals; normal exit, nonzero, closed streams, repeated running/cleanup cancellation and surviving descendant; lost anchor forbids signal and solver answer')
