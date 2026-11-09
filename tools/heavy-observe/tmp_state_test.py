#!/usr/bin/env python3
"""Retention limits and actual ordinary Heavy build lifecycle."""
import contextlib
import importlib.machinery
import importlib.util
import io
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_inventory import check as check_inventory
loader = importlib.machinery.SourceFileLoader('fren_build_test', str(ROOT / 'scripts/fren-build'))
spec = importlib.util.spec_from_loader(loader.name, loader)
build = importlib.util.module_from_spec(spec)
loader.exec_module(build)


def main():
    # A manually invoked control is insufficient: the default driver must
    # schedule it, and its focused-job dispatcher must accept it too.
    check_inventory((ROOT / 'src/FrenTestMain.lean').read_text())
    parent = ROOT / 'tools/heavy-observe/test-work'
    parent.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='tmp-state-', dir=parent) as temp:
        work = Path(temp).resolve()
        store = work / 'retention'; store.mkdir()
        old = store / 'fren-build-old'; old.mkdir(); (old / 'data').write_bytes(b'old')
        stale = time.time() - build.RETENTION_AGE - 1
        os.utime(old, (stale, stale))
        newer = store / 'fren-build-newer'; newer.mkdir(); (newer / 'data').write_bytes(b'123456')
        active = store / '.active-fixture'; active.mkdir(); (active / 'data').write_bytes(b'abcdef')
        build.RETENTION_BYTES = 8
        with contextlib.redirect_stderr(io.StringIO()) as stderr:
            build.finish_private_state(active, False)
        retained = store / 'fren-build-fixture'
        assert retained.is_dir() and (retained / 'data').read_bytes() == b'abcdef'
        assert not old.exists() and not newer.exists()
        assert str(retained) in stderr.getvalue()
        oversized = store / '.active-large'; oversized.mkdir(); (oversized / 'large').write_bytes(b'0123456789')
        with contextlib.redirect_stderr(io.StringIO()): build.finish_private_state(oversized, False)
        assert (store / 'fren-build-large').is_dir()
        assert sum(p.stat().st_size for p in store.rglob('*') if p.is_file()) <= 8
        success = store / '.active-success'; success.mkdir()
        build.finish_private_state(success, True)
        assert not success.exists()

        home = work / 'home'; home.mkdir()
        pkg = work / 'pkg'; pkg.mkdir()
        (pkg / 'lean-toolchain').write_bytes((ROOT / 'lean-toolchain').read_bytes())
        (pkg / 'lakefile.toml').write_text('name = "tiny"\nenableArtifactCache = false\n[[lean_lib]]\nname = "Tiny"\n')
        (pkg / 'Tiny.lean').write_text('def tiny : Nat := 42\n')
        env = dict(os.environ, HOME=str(home), LAKE_CACHE_DIR=str(work / 'lake-cache'),
                   HEAVY_MAX_LOAD='off', HEAVY_MEM_GB='2', HEAVY_SLOTS='1')
        for key in ('HEAVY_BUDGET_DIR', 'LEAN_SYSROOT', 'LAKE_OVERRIDE_LEAN', 'PYTHONPATH',
                    'HEAVY_TEST_STATE_CAPTURE', 'FREN_BUILD_REQUESTS_FILE'):
            env.pop(key, None)
        trace = work / 'mkdir.trace'
        command = [str(ROOT / 'scripts/heavy'), 'lake', '-d', str(pkg), 'build', '+Tiny', '--offline', '--no-cache']
        tracer = shutil.which('strace')
        scratch = work / 'tmp'; scratch.mkdir()
        if not tracer:
            # The same mkdtemp leak is observable in an isolated TMPDIR on
            # systems without strace; the traced path checks the default /tmp.
            env['TMPDIR'] = str(scratch)
        observed = [tracer, '-f', '-e', 'trace=mkdir,mkdirat', '-o', str(trace), *command] if tracer else command
        ok = subprocess.run(observed,
                            env=env, capture_output=True, text=True, timeout=90)
        assert ok.returncode == 0, (ok.stdout, ok.stderr)
        if tracer:
            assert '/tmp/fren-build-' not in trace.read_text()
        else:
            assert not list(scratch.glob('fren-build-*'))
        state_root = home / '.cache/heavy/build-state'
        assert not list(state_root.glob('.active-*')) and not list(state_root.glob('fren-build-*'))
        assert 'retained private state:' not in ok.stderr
        fail = subprocess.run(command[:-3] + ['missing-target', '--offline', '--no-cache'], env=env,
                              capture_output=True, text=True, timeout=90)
        assert fail.returncode != 0, (fail.stdout, fail.stderr)
        match = re.search(r'fren-build: retained private state: ([^\n]+)', fail.stderr)
        assert match, fail.stderr
        state = Path(match[1]); assert state.is_dir() and state.parent == state_root
        assert not list(state_root.glob('.active-*'))
        print('tmp-state controls passed; success cleaned, failure retained on disk')


if __name__ == '__main__': main()
