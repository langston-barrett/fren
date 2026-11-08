#!/usr/bin/env python3
"""Fren2 batch deadline controller and its process-level regression.

`--run` is the production entry point and always uses 30 seconds. The other
entry points are fixtures used only by the registered regression below.
"""
import array
import ctypes
import json
import math
import os
from pathlib import Path
import select
import shutil
import socket
import signal
import subprocess
import sys
import tempfile
import time


def control(command, seconds, parent_pid):
    """Own one group, retaining its waitable leader until the final signal."""
    if (sys.platform != 'linux' or not hasattr(os, 'pidfd_open')
            or not hasattr(signal, 'pthread_sigmask')):
        print('fren2_test: Linux pidfds and signal masks are required', file=sys.stderr)
        return 125
    child = None
    parent_fd = child_fd = wake_read = wake_write = None
    cancellation = []
    reason = None
    result = 125
    try:
        if os.getppid() != parent_pid:
            raise RuntimeError('runner disappeared before controller startup')
        # Same Linux subreaper facility used by scripts/heavy's child_subreaper.
        prctl = ctypes.CDLL(None, use_errno=True).prctl
        if prctl(36, 1, 0, 0, 0) != 0:
            raise OSError(ctypes.get_errno(), 'cannot enable subreaper')
        if signal.getsignal(signal.SIGCHLD) != signal.SIG_DFL:
            raise RuntimeError('default SIGCHLD disposition required')
        parent_fd = os.pidfd_open(parent_pid)
        if os.getppid() != parent_pid:
            raise RuntimeError('runner disappeared before controller startup')
        wake_read, wake_write = os.pipe2(os.O_NONBLOCK | os.O_CLOEXEC)
        signal.set_wakeup_fd(wake_write)
        def cancelled(signum, _frame):
            if not cancellation:
                cancellation.append(signum)
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            signal.signal(sig, cancelled)
        start = time.monotonic()
        # A cancellation must not land between fork and retaining the child.
        blocked = (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)
        previous = signal.pthread_sigmask(signal.SIG_BLOCK, blocked)
        try:
            child = subprocess.Popen(command, start_new_session=True,
                                     preexec_fn=lambda: signal.pthread_sigmask(signal.SIG_SETMASK, previous))
            child_fd = os.pidfd_open(child.pid)
        finally:
            signal.pthread_sigmask(signal.SIG_SETMASK, previous)
        poll = select.poll()
        poll.register(parent_fd, select.POLLIN)
        poll.register(child_fd, select.POLLIN)
        poll.register(wake_read, select.POLLIN)
        while True:
            if cancellation:
                break
            remaining = start + seconds - time.monotonic()
            if remaining <= 0:
                reason = 'deadline'
                break
            ready = dict(poll.poll(math.ceil(remaining * 1000)))
            if wake_read in ready:
                continue
            if parent_fd in ready:
                reason = 'runner exited'
                break
            if child_fd in ready:
                # WNOWAIT keeps the leader's PID and process group anchored.
                observed = os.waitid(os.P_PID, child.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
                if observed is None:
                    raise RuntimeError('child readiness without exit status')
                result = observed.si_status if observed.si_code == os.CLD_EXITED else 128 + observed.si_status
                break
    except (OSError, RuntimeError, ValueError, AttributeError) as e:
        reason = f'control failure: {e}'
        result = 125
    finally:
        # No reentrant signal may reap the leader or interrupt owned cleanup.
        signal.pthread_sigmask(signal.SIG_BLOCK, (signal.SIGINT, signal.SIGTERM, signal.SIGHUP))
        if child is not None:
            killed = True
            try:
                # The unreaped direct child anchors the numeric process group.
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            except OSError as e:
                reason = f'control failure during cleanup: {e}'
                result = 125
                killed = False
            try:
                # A subreaper adopts orphaned same-group descendants. No further
                # group signals occur after the leader is reaped.
                while True:
                    pid, _ = os.waitpid(-child.pid, 0 if killed else os.WNOHANG)
                    if pid == 0:
                        break
            except ChildProcessError:
                pass
            except OSError as e:
                reason = f'control failure while reaping: {e}'
                result = 125
        pending = signal.sigpending()
        if not cancellation:
            cancellation.extend(sig for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP) if sig in pending)
        if wake_write is not None:
            signal.set_wakeup_fd(-1)
        for fd in (child_fd, parent_fd, wake_read, wake_write):
            if fd is not None:
                os.close(fd)
    if cancellation and not (reason and reason.startswith('control failure')):
        reason = f'controller received signal {int(cancellation[0])}'
        result = 128 + int(cancellation[0])
    if reason:
        print(f'fren2_test: {reason}', file=sys.stderr, flush=True)
        if reason == 'deadline':
            return 124
        if reason == 'runner exited':
            return 125
    return result


def publish(role):
    # The fixture sends a pidfd for itself and stays alive until acknowledged.
    # The harness never has to reacquire an identity from a numeric PID.
    with socket.socket(socket.AF_UNIX, socket.SOCK_SEQPACKET) as connection:
        connection.connect(os.environ['FREN2_TEST_SOCKET'])
        fd = os.pidfd_open(os.getpid())
        try:
            connection.sendmsg([role.encode()], [(socket.SOL_SOCKET, socket.SCM_RIGHTS, array.array('i', [fd]))])
        finally:
            os.close(fd)
        if connection.recv(1) != b'!':
            raise RuntimeError('fixture identity was not acknowledged')


def fixture(mode):
    publish('leader')
    if mode == 'success':
        print('fixture stdout', flush=True)
        print('fixture stderr', file=sys.stderr, flush=True)
        return 0
    if mode == 'context':
        print(json.dumps([os.getcwd(), sys.argv[1:], os.environ['FREN2_TEST_MARKER']]), flush=True)
        return 0
    if mode == 'stream':
        print('stream ready', flush=True)
        while True: time.sleep(1)
    if mode == 'failure':
        return 7
    if mode == 'signal':
        os.kill(os.getpid(), signal.SIGTERM)
    if mode in ('orphan', 'stopped'):
        ready_read, ready_write = os.pipe()
        if os.fork() == 0:
            os.close(ready_read)
            publish('descendant')
            os.write(ready_write, b'!')
            os.close(ready_write)
            while True: time.sleep(1)
        os.close(ready_write)
        assert os.read(ready_read, 1) == b'!'
        os.close(ready_read)
        if mode == 'orphan': return 0
        os.killpg(os.getpgrp(), signal.SIGSTOP)
    while True: time.sleep(1)


def receive_identity(listener, role, before_ack=None):
    with listener.accept()[0] as connection:
        data, ancillary, flags, _ = connection.recvmsg(64, socket.CMSG_SPACE(array.array('i').itemsize))
        fds = array.array('i')
        for level, kind, payload in ancillary:
            if level == socket.SOL_SOCKET and kind == socket.SCM_RIGHTS:
                fds.frombytes(payload[:len(payload) - len(payload) % fds.itemsize])
        if data != role.encode() or flags & socket.MSG_CTRUNC or len(fds) != 1:
            for fd in fds: os.close(fd)
            raise RuntimeError('incomplete fixture identity')
        try:
            if before_ack is not None: before_ack(fds[0])
            connection.sendall(b'!')
        except BaseException:
            os.close(fds[0])
            raise
        return fds[0]


def test(runner):
    script = str(Path(__file__).resolve())
    with tempfile.TemporaryDirectory() as tmp, socket.socket(socket.AF_UNIX, socket.SOCK_SEQPACKET) as listener:
        listener.bind(str(Path(tmp) / 'identities'))
        listener.listen()
        listener.settimeout(2)
        env = dict(os.environ, FREN2_TEST_SOCKET=listener.getsockname(), FREN2_TEST_MARKER='inherited')
        processes, identities = [], []
        def receive(role):
            fd = receive_identity(listener, role)
            identities.append(fd)
            return fd
        def spawn(args):
            p = subprocess.Popen(args, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            processes.append(p)
            return p
        def invoke(mode, seconds=.35):
            p = spawn([sys.executable, script, '--test-control', str(seconds),
                str(os.getpid()), sys.executable, script, '--fixture', mode])
            return p, receive('leader')
        def dead(fd):
            # A held pidfd cannot silently change identity after PID reuse.
            info = Path(f'/proc/self/fdinfo/{fd}').read_text().splitlines()
            assert 'Pid:\t-1' in info, f'owned process was not reaped: {info}'
        def finish(p, expected):
            out, err = p.communicate(timeout=4)
            assert p.returncode == expected, (p.returncode, out, err)
            print(f'fixture {p.args[-1]} status={p.returncode}', flush=True)
            return out, err
        try:
            print('controls: normal success, status and streams', flush=True)
            p, leader = invoke('success'); out, err = finish(p, 0); dead(leader)
            assert out == 'fixture stdout\n' and err == 'fixture stderr\n'
            p, leader = invoke('context'); out, _ = finish(p, 0); dead(leader)
            assert json.loads(out) == [os.getcwd(), ['--fixture', 'context'], 'inherited']
            p, leader = invoke('stream'); assert p.stdout.readline() == 'stream ready\n' and p.poll() is None
            finish(p, 124); dead(leader)
            p, leader = invoke('failure'); finish(p, 7); dead(leader)
            p, leader = invoke('signal'); finish(p, 143); dead(leader)
            foreign = spawn([sys.executable, '-c', 'import time; time.sleep(20)'])
            print('controls: stopped group, repeated stop/resume, orphan and foreign peer', flush=True)
            start = time.monotonic(); p, leader = invoke('stopped'); descendant = receive('descendant')
            _, err = finish(p, 124); elapsed = time.monotonic() - start
            assert 'deadline' in err and elapsed < 3
            dead(leader); dead(descendant)
            p, leader = invoke('sleep', .6)
            for _ in range(4):
                signal.pidfd_send_signal(leader, signal.SIGSTOP); time.sleep(.025)
                signal.pidfd_send_signal(leader, signal.SIGCONT); time.sleep(.025)
            _, err = finish(p, 124); assert 'deadline' in err; dead(leader)
            # A held pidfd remains tied to the original process after expiry.
            try:
                signal.pidfd_send_signal(leader, signal.SIGCONT)
                raise AssertionError('signal unexpectedly reached a reaped fixture')
            except ProcessLookupError:
                print('expired pidfd refused signal: ESRCH', flush=True)
            p, leader = invoke('orphan', 2); descendant = receive('descendant')
            finish(p, 0); dead(leader); dead(descendant)
            assert foreign.poll() is None
            print('controls: controller cancellation and runner death', flush=True)
            p, leader = invoke('sleep', 5); p.terminate(); finish(p, 143); dead(leader)
            parent = spawn([sys.executable, script, '--test-parent', script])
            leader = receive('leader')
            parent.terminate(); parent.communicate(timeout=4)
            assert parent.returncode == -signal.SIGTERM; dead(leader)
            print(f'runner termination status={parent.returncode}; owned child reaped', flush=True)
            assert foreign.poll() is None
            # A failed handoff must still terminate and wait for its owned parent.
            parent = spawn([sys.executable, script, '--test-parent', script])
            captured = []
            def fail_before_ack(fd):
                captured.append(os.dup(fd))
                identities.append(captured[-1])
                raise RuntimeError('forced readiness failure')
            try:
                receive_identity(listener, 'leader', before_ack=fail_before_ack)
                raise AssertionError('forced readiness failure was not raised')
            except RuntimeError as e:
                assert str(e) == 'forced readiness failure'
            finally:
                parent.terminate(); parent.communicate(timeout=4)
            assert len(captured) == 1
            dead(captured[0])
            print('forced readiness failure: parent waited and fixture reaped', flush=True)
            # A partial handoff without a descriptor is rejected, with no PID parsing.
            sender, receiver = socket.socketpair(type=socket.SOCK_SEQPACKET)
            with sender, receiver:
                sender.sendall(b'le')
                class OneConnection:
                    def accept(self): return receiver, None
                try:
                    receive_identity(OneConnection(), 'leader')
                    raise AssertionError('partial identity accepted')
                except RuntimeError as e:
                    assert str(e) == 'incomplete fixture identity'
            print('partial handoff rejected', flush=True)
            print('controls: cleanup-entry cancellation', flush=True)
            for mode in ('normal', 'cancel'):
                p = spawn([sys.executable, script, '--test-cleanup', mode])
                leader = receive('leader')
                if mode == 'normal':
                    descendant = receive('descendant')
                else:
                    p.terminate()
                _, err = finish(p, 143)
                assert 'cleanup-entry signals' in err and 'cleanup-blocked signals' in err
                print(f'{mode}: real signals at cleanup entry and during blocked cleanup; status 143', flush=True)
                dead(leader)
                if mode == 'normal': dead(descendant)
        finally:
            for p in reversed(processes):
                if p.poll() is None: p.terminate()
                try: p.communicate(timeout=7)
                except subprocess.TimeoutExpired:
                    p.kill(); p.communicate()
            for fd in identities: os.close(fd)
        print('controls: exact environment through production entry', flush=True)
        env_tool = shutil.which('env')
        assert env_tool is not None
        for mode, original in [('unset', ''), ('set', 'warn')]:
            expected = dict(env, LC_CTYPE='C')
            if mode == 'set': expected['PYTHONCOERCECLOCALE'] = original
            else: expected.pop('PYTHONCOERCECLOCALE', None)
            launch = dict(expected, PYTHONCOERCECLOCALE='0')
            env_result = subprocess.run([sys.executable, script, '--run', str(os.getpid()),
                mode, original, env_tool, '-0'], env=launch, capture_output=True)
            assert env_result.returncode == 0, env_result.stderr
            actual = dict(entry.split('=', 1) for entry in env_result.stdout.decode().split('\0') if entry)
            assert actual == expected, (actual, expected)
        print('controls: control failures and public dispatch', flush=True)
        unsupported = subprocess.run([sys.executable, '-c',
            "import runpy,sys; m=runpy.run_path(sys.argv[1]); sys.platform='unsupported'; "
            "sys.exit(m['control']([],1,0))", script], capture_output=True, text=True)
        assert unsupported.returncode == 125 and 'required' in unsupported.stderr
        failed = subprocess.run([sys.executable, script, '--test-control', '1', str(os.getpid()),
                                 str(Path(tmp) / 'absent')], capture_output=True, text=True)
        assert failed.returncode == 125 and 'control failure' in failed.stderr
        absent_env = dict(os.environ, PATH=str(Path(tmp) / 'absent'))
        failed = subprocess.run([runner, '--job', 'resolver'], env=absent_env, capture_output=True, text=True)
        assert failed.returncode != 0 and 'python3' in failed.stderr
        p = subprocess.run([runner, '--job', 'resolver'], capture_output=True, text=True)
        assert p.returncode == 0 and 'resolver cases:' in p.stdout, (p.returncode, p.stderr)
        elsewhere = subprocess.run([runner, '--job', 'resolver'], cwd=tmp, capture_output=True, text=True)
        assert elsewhere.returncode != 0 and "test/FrenResolve/s1.fren" in elsewhere.stderr
        p = subprocess.run([runner, '--lib', 'missing'], capture_output=True, text=True)
        assert p.returncode == 2 and 'unknown or ambiguous' in p.stderr
        p = subprocess.run([runner, '--fren2-internal-job', '--job', 'resolver'], capture_output=True, text=True)
        assert p.returncode == 125
        print(f'deadline controls passed; stopped-group timeout {elapsed:.3f}s, orphan and foreign controls passed')


if __name__ == '__main__':
    if len(sys.argv) >= 7 and sys.argv[1] == '--run':
        if sys.argv[3] == 'set':
            os.environ['PYTHONCOERCECLOCALE'] = sys.argv[4]
        elif sys.argv[3:5] == ['unset', '']:
            os.environ.pop('PYTHONCOERCECLOCALE', None)
        else:
            print('fren2_test: invalid controller environment', file=sys.stderr)
            sys.exit(125)
        sys.exit(control(sys.argv[5:], 30, int(sys.argv[2])))
    if len(sys.argv) >= 5 and sys.argv[1] == '--test-control':
        sys.exit(control(sys.argv[4:], float(sys.argv[2]), int(sys.argv[3])))
    if len(sys.argv) == 3 and sys.argv[1] == '--fixture':
        sys.exit(fixture(sys.argv[2]))
    if len(sys.argv) == 3 and sys.argv[1] == '--test-cleanup':
        source = Path(__file__).read_text().splitlines()
        entry = source.index('        # No reentrant signal may reap the leader or interrupt owned cleanup.') + 2
        blocked = source.index('                os.killpg(child.pid, signal.SIGKILL)') + 1
        fired = set()
        def at_cleanup(frame, event, _arg):
            if event == 'line' and frame.f_code is control.__code__ and frame.f_lineno in (entry, blocked) and frame.f_lineno not in fired:
                fired.add(frame.f_lineno)
                label = 'cleanup-entry signals' if frame.f_lineno == entry else 'cleanup-blocked signals'
                print(label, file=sys.stderr, flush=True)
                for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP): os.kill(os.getpid(), sig)
            return at_cleanup
        sys.settrace(at_cleanup)
        mode = 'orphan' if sys.argv[2] == 'normal' else 'sleep'
        sys.exit(control([sys.executable, str(Path(__file__).resolve()), '--fixture', mode], 5, os.getppid()))
    if len(sys.argv) == 3 and sys.argv[1] == '--test-parent':
        subprocess.Popen([sys.executable, sys.argv[2], '--test-control', '5', str(os.getpid()),
                          sys.executable, sys.argv[2], '--fixture', 'sleep'])
        while True: time.sleep(1)
    if len(sys.argv) == 2:
        test(str(Path(sys.argv[1]).resolve()))
    else:
        print('fren2_test: invalid deadline controller arguments', file=sys.stderr)
        sys.exit(125)
