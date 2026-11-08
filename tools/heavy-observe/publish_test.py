#!/usr/bin/env python3
"""Focused spool boundaries; records here are synthetic, not compiler runs."""
import concurrent.futures
import fcntl
import importlib.util
import json
import os
import signal
import select
import subprocess
import sys
from pathlib import Path
import tempfile
import time
import unittest

spec = importlib.util.spec_from_file_location('publisher', Path(__file__).with_name('publish.py'))
p = importlib.util.module_from_spec(spec); spec.loader.exec_module(p)


def raw(**changes):
    now = time.monotonic_ns()
    r = dict(schema=3, family='lean', input_kind='file', source='Input.lean', cwd='/work',
             source_before='digest', source_after='digest', real_compiler='/tool/lean',
             compiler_fingerprint='compiler', compiler_version='version', compiler_githash='hash',
             args=['Input.lean', '-o', 'out'], setup=None, setup_fingerprint=None,
             boot_id=Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
             launch_errno=0, exec_errno=0, wait_errno=0, clock_errno=0, raw_wait_status=0,
             gate_errno=0, wrapper_code=0, child_present=True, child_pid=os.getpid(),
             start_monotonic_ns=now-1, end_monotonic_ns=now, peak_rss_kib=100,
             measured_peak_rss_kib=100)
    r.update(changes)
    return json.dumps(r, separators=(',', ':')).encode()


class Spool(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.home = Path(self.tmp.name)
        self.spool = self.home / '.cache/heavy/compiler-observations'

    def files(self): return list(self.spool.glob('*.json'))
    def put(self, r): return p.publish(r, str(self.home))

    def owned(self, command, *, env=None, timeout=15):
        child = subprocess.Popen(command, env=env, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, start_new_session=True)
        try:
            out, err = child.communicate(timeout=timeout)
            return subprocess.CompletedProcess(command, child.returncode, out, err)
        except subprocess.TimeoutExpired:
            # Signal only our session controller; its budget child group is
            # separately owned and cleaned by the controller's cancellation.
            try: os.kill(child.pid, signal.SIGTERM)
            except ProcessLookupError: pass
            try: child.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                try: os.kill(child.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                child.communicate(timeout=5)
            raise

    def test_interrupted_pending_recovery(self):
        sample = self.home / 'raw.json'; sample.write_bytes(raw())
        code = """import importlib.util,os,sys
s=importlib.util.spec_from_file_location('p',sys.argv[1]); p=importlib.util.module_from_spec(s); s.loader.exec_module(p)
link=os.link
def crash(*a,**kw):
 if sys.argv[4]=='after': link(*a,**kw)
 os._exit(91)
os.link=crash
p.publish(open(sys.argv[2],'rb').read(),sys.argv[3])
"""
        for point in ('before', 'after'):
            home = self.home / point; home.mkdir()
            result = self.owned([sys.executable, '-c', code, p.__file__, str(sample), str(home), point])
            self.assertEqual(result.returncode, 91, result.stderr)
            spool = home / '.cache/heavy/compiler-observations'
            self.assertEqual(len(list(spool.glob('.pending-*'))), 1)
            self.assertTrue(p.publish(sample.read_bytes(), str(home)))
            self.assertFalse(list(spool.glob('.pending-*')))
            for _ in range(3): self.assertTrue(p.publish(raw(), str(home)))
            self.assertEqual(len(list(spool.glob('*.json'))), 2)

    def test_incomplete_pending_recovery(self):
        self.put(raw())
        partial = self.spool / ('.pending-' + 'b' * 32)
        partial.write_bytes(b'{"schema":')
        partial.chmod(0o600)
        self.assertTrue(self.put(raw()))
        self.assertFalse(partial.exists())
        self.assertEqual(len(self.files()), 2)

    def test_pending_symlink_rejected(self):
        self.put(raw())
        (self.spool / ('.pending-' + 'a' * 32)).symlink_to('/etc/passwd')
        with self.assertRaises(OSError): self.put(raw())

    def test_selection_and_retention(self):
        for _ in range(4): self.assertTrue(self.put(raw()))
        self.assertEqual(len(self.files()), 2)
        for i in range(130):
            name = f'{i}.lean'
            self.put(raw(source=name, args=[name]))
        self.assertEqual(len(self.files()), 128)
        self.assertLessEqual(sum(x.stat().st_size for x in self.files()), p.LIMIT)
        self.assertEqual(self.spool.stat().st_mode & 0o777, 0o700)

    def test_total_byte_budget(self):
        old = p.LIMIT
        p.LIMIT = 1600
        self.addCleanup(setattr, p, 'LIMIT', old)
        for i in range(10):
            name = f'{i}.lean'
            self.put(raw(source=name, args=[name]))
        self.assertLessEqual(sum(f.stat().st_size for f in self.files()), 1600)
        self.assertTrue(self.files())

    def test_rejected_status_and_context(self):
        for change in [dict(schema=3.0), dict(raw_wait_status=256), dict(clock_errno=1), dict(boot_id='foreign'),
                       dict(source_after='changed'), dict(child_present=False), dict(args=['--run', 'Input.lean']),
                       dict(end_monotonic_ns=0), dict(measured_peak_rss_kib=0), dict(setup='x')]:
            self.assertFalse(self.put(raw(**change)), change)
        self.assertFalse(self.spool.exists())

    def test_age_boundary(self):
        r = p.decode(raw(start_monotonic_ns=1, end_monotonic_ns=1))
        self.assertIsNotNone(p.cohort(r, r['boot_id'], p.AGE + 1))
        self.assertIsNone(p.cohort(r, r['boot_id'], p.AGE + 2))

    def test_concurrent(self):
        rows = [raw() for _ in range(24)]
        with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
            list(pool.map(self.put, rows))
        self.assertEqual(len(self.files()), 2)
        for f in self.files(): self.assertIsNotNone(p.cohort(p.decode(f.read_bytes()), Path('/proc/sys/kernel/random/boot_id').read_text().strip(), time.monotonic_ns()))

    def test_busy_lock_times_out(self):
        self.put(raw())
        with open(self.spool / '.lock', 'rb') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            with self.assertRaises(TimeoutError): self.put(raw())

    def test_foreign_symlink_corruption(self):
        self.put(raw())
        file = self.files()[0]; file.unlink(); file.symlink_to('/etc/passwd')
        with self.assertRaises(OSError): self.put(raw())
        file.unlink(); self.put(raw()); file = self.files()[0]; file.write_bytes(b'{}')
        with self.assertRaises(ValueError): self.put(raw())

    def test_observer_publisher_failure_preserves_status(self):
        base = Path(__file__).resolve().parent
        spec = importlib.util.spec_from_file_location('overlay', base / 'overlay.py')
        overlay = importlib.util.module_from_spec(spec); spec.loader.exec_module(overlay)
        real = Path(subprocess.check_output(['elan', 'which', 'lean'], text=True).strip()).resolve()
        root = self.home / 'overlay'
        overlay.create(root, real, base / '.lake/build/bin/heavy_observe')
        manifest = self.home / 'requests'; manifest.write_text('')
        source = self.home / 'Valid.lean'; source.write_text('def answer : Nat := 42\n')
        env = dict(os.environ, HEAVY_OBSERVE_DIR=str(root / 'records'),
                   HEAVY_OBSERVE_PUBLISHER=str(self.home / 'missing-publisher'),
                   HEAVY_COMPILER_CPU_SECONDS='120', HEAVY_COMPILER_WALL_MS='180000')
        session = base / '.lake/build/bin/budget_session'
        command = [str(session), str(self.home / 'session'), '1100000', '100000',
                   '600000', '30000', str(manifest), '--', sys.executable, '-c',
                   'import subprocess,sys; sys.exit(subprocess.call(sys.argv[1:]))',
                   str(root / 'bin/lean'), str(source)]
        result = self.owned(command, env=env, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b'optional publication failed', result.stderr)
        records = [json.loads(x.read_bytes()) for x in (root / 'records').glob('*.json')]
        files = [r for r in records if r['input_kind'] == 'file']
        self.assertEqual(len(files), 1)
        self.assertEqual((files[0]['raw_wait_status'], files[0]['wrapper_code']), (0, 0))
        self.assertEqual(files[0]['request_provenance'], 'explicit-unknown-fallback')

    def test_stalled_publisher_and_cancellation(self):
        base = Path(__file__).resolve().parent
        spec = importlib.util.spec_from_file_location('overlay', base / 'overlay.py')
        overlay = importlib.util.module_from_spec(spec); spec.loader.exec_module(overlay)
        real = Path(subprocess.check_output(['elan', 'which', 'lean'], text=True).strip()).resolve()
        root = self.home / 'stall-overlay'
        overlay.create(root, real, base / '.lake/build/bin/heavy_observe')
        manifest = self.home / 'requests'; manifest.write_text('')
        source = self.home / 'Valid.lean'; source.write_text('def answer : Nat := 42\n')
        marker = self.home / 'started'
        helper = self.home / 'stall.py'
        helper.write_text('import os,time\nfrom pathlib import Path\np=Path(os.environ["PUBLISH_MARKER"])\nt=p.with_suffix(".tmp")\nt.write_text(str(os.getpid()) + " " + str(os.getppid()))\nos.replace(t,p)\ntime.sleep(60)\n')
        env = dict(os.environ, HEAVY_OBSERVE_DIR=str(root / 'records'),
                   HEAVY_OBSERVE_PUBLISHER=str(helper), PUBLISH_MARKER=str(marker),
                   HEAVY_COMPILER_CPU_SECONDS='120', HEAVY_COMPILER_WALL_MS='180000')
        for label in ('timeout', 'cancel'):
            marker.unlink(missing_ok=True)
            before = set((root / 'records').glob('*.json'))
            session = base / '.lake/build/bin/budget_session'
            command = [str(session), str(self.home / ('session-' + label)), '1100000', '100000',
                       '600000', '30000', str(manifest), '--', sys.executable, '-c',
                       'import subprocess,sys; sys.exit(subprocess.call(sys.argv[1:]))',
                       str(root / 'bin/lean'), str(source)]
            child = subprocess.Popen(command, env=env, stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE, start_new_session=True)
            pidfd = observer_fd = None
            try:
                deadline = time.monotonic() + 10
                while not marker.exists() and child.poll() is None and time.monotonic() < deadline:
                    time.sleep(.01)
                self.assertTrue(marker.exists(), 'publisher did not start')
                helper_pid, observer_pid = map(int, marker.read_text().split())
                pidfd = os.pidfd_open(helper_pid)
                observer_fd = os.pidfd_open(observer_pid)
                records = list(set((root / 'records').glob('*.json')) - before)
                self.assertEqual(len(records), 1)
                row = json.loads(records[0].read_bytes())
                self.assertEqual((row['raw_wait_status'], row['wrapper_code'], row['child_present']), (0, 0, True))
                if label == 'cancel': signal.pidfd_send_signal(observer_fd, signal.SIGTERM)
                out, err = child.communicate(timeout=10)
                if label == 'timeout':
                    self.assertEqual(child.returncode, 0, err)
                    self.assertIn(b'optional publication failed', err)
                else:
                    self.assertNotEqual(child.returncode, 0)
                poller = select.poll(); poller.register(pidfd, select.POLLIN)
                self.assertTrue(poller.poll(2000), 'publisher survived observer')
                self.assertFalse(Path(f'/proc/{helper_pid}').exists(), f'publisher was not reaped ({label}): ' + (Path(f'/proc/{helper_pid}/status').read_text() if Path(f'/proc/{helper_pid}').exists() else 'gone'))
            finally:
                if child.poll() is None:
                    try: os.kill(child.pid, signal.SIGTERM)
                    except ProcessLookupError: pass
                    try: child.communicate(timeout=5)
                    except subprocess.TimeoutExpired:
                        try: os.kill(child.pid, signal.SIGKILL)
                        except ProcessLookupError: pass
                        child.communicate(timeout=5)
                if observer_fd is not None: os.close(observer_fd)
                if pidfd is not None: os.close(pidfd)

    def test_oversize_and_duplicate(self):
        with self.assertRaises(ValueError): self.put(b' ' * (p.MAX_RECORD + 1))
        with self.assertRaises(ValueError): self.put(b'{"schema":3,"schema":3}')

if __name__ == '__main__': unittest.main()
