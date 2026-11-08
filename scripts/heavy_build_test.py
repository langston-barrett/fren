#!/usr/bin/env python3
"""Bounded ordinary Heavy dispatch controls using the real session controller.

Run under Heavy offline with prebuilt heavy_observe/budget_session. All nested
Heavy instances use private test state. --output retains source/status/timings.
The one existing-target compilation is a separate explicit validation command.
"""
import argparse
import hashlib
import importlib.machinery
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
from unittest import mock

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
HEAVY = ROOT / 'scripts/heavy'


def load(path):
    loader = importlib.machinery.SourceFileLoader(path.name.replace('-', '_'), str(path))
    spec = importlib.util.spec_from_loader(loader.name, loader)
    module = importlib.util.module_from_spec(spec)
    loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    work = args.output
    assert work.is_absolute()
    work.mkdir(mode=0o700)
    results = []
    build = load(ROOT / 'scripts/fren-build')
    heavy = load(HEAVY)
    real = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip()) / 'bin/lean'
    real = real.resolve(strict=True)
    pin = (ROOT / 'lean-toolchain').read_text().strip()
    # Discovery and dispatch use raw argv, not shell text or substring matches.
    for command in (['lake', 'build'], ['lake', '--no-cache', 'build', 'space target'],
                    ['lake', '-d', str(work), 'build'], ['lake', '-K', 'build', 'build'],
                    ['lake', '+' + pin, 'build']):
        assert build.lake_build(command) is not None, command
    for command in (['lake', 'env', 'build'], ['lake', '-d', 'build', 'env'],
                    ['lake', '--help', 'build'], ['lake', '-o', 'build', 'env'],
                    ['lake', '--service', 'build', 'env'], ['echo', 'lake', 'build']):
        assert build.lake_build(command) is None, command
    boot = ['lake', '-d', str(ROOT / 'tools/heavy-observe'), 'build', 'budget_session']
    assert build.heavy_command(boot, 1000000) == boot
    assert build.outer_allowance(1000000) <= 900000
    with mock.patch.object(build.Path, 'read_text', return_value='0::/../bad\n'):
        try:
            build.outer_allowance(1000000)
            raise AssertionError('accepted unresolved cgroup')
        except ValueError:
            pass
    # Compute the ceiling from raw ancestor bytes, including a tighter parent.
    def cgroup_text(path, *args, **kwargs):
        if str(path) == '/proc/self/cgroup':
            return '0::/control/job\n'
        return str((500000 if path.parent.name == 'job' else 400000) * 1024)
    with mock.patch.object(build.Path, 'read_text', cgroup_text), \
         mock.patch.object(build.Path, 'is_dir', return_value=True), \
         mock.patch.object(build.Path, 'exists', return_value=True):
        assert build.outer_allowance(2000000) == 300000
    fake = work / 'bin'; fake.mkdir()
    (fake / 'lean').symlink_to(real)
    lake = fake / 'lake'
    lake.write_text('#!' + sys.executable + '\n' + r'''
import json, os, pathlib, signal, subprocess, sys, time
mode = os.environ.get('CONTROL', 'argv')
if mode == 'assert-gated':
    sys.exit(0 if os.environ.get('HEAVY_BUDGET_DIR') else 19)
if mode == 'missing':
    lean = (pathlib.Path(os.environ['LEAN_SYSROOT']) / 'bin/lean'
            if os.environ.get('HEAVY_BUDGET_DIR') else pathlib.Path(__file__).parent / 'lean')
    sys.exit(subprocess.call([str(lean), 'Missing-source.lean']))
if mode == 'signal':
    os.kill(os.getpid(), signal.SIGTERM)
if mode in ('wait', 'memory'):
    size = 224 * 1024 * 1024 if mode == 'memory' else 1024
    child = subprocess.Popen([sys.executable, '-c',
        'import pathlib,sys,time; x=bytearray(int(sys.argv[1])); '
        'pathlib.Path(sys.argv[2]).write_text(str(__import__("os").getpid())); time.sleep(30)',
        str(size), os.environ['READY']])
    sys.exit(child.wait())
print(json.dumps({'argv': sys.argv[1:], 'cwd': os.getcwd(),
    'sentinel': os.environ.get('SENTINEL'), 'stdin': sys.stdin.read(),
    'budget': os.environ.get('HEAVY_BUDGET_DIR'), 'sysroot': os.environ.get('LEAN_SYSROOT'),
    'net': os.readlink('/proc/self/ns/net')}), flush=True)
if mode == 'pipes':
    sys.stdout.write('O' * 131072); sys.stdout.flush()
    sys.stderr.write('E' * 131072); sys.stderr.flush()
sys.exit(int(os.environ.get('STATUS', '0')))
''')
    lake.chmod(0o755)
    env = dict(os.environ, HOME=str(work / 'home'), TMPDIR=str(work),
               ELAN_HOME=os.environ.get('ELAN_HOME', '/opt/elan'),
               HEAVY_MEM_GB='1.5', HEAVY_SLOTS='1', HEAVY_MAX_LOAD='off',
               SENTINEL='space λ $literal')
    for key in ('HEAVY_BUDGET_DIR', 'LEAN_SYSROOT', 'LAKE_OVERRIDE_LEAN',
                'HEAVY_OBSERVE_DIR', 'HEAVY_LOG', 'FREN_BUILD_REQUESTS_FILE',
                'FREN_BUILD_ALLOWANCE_KIB', 'FREN_BUILD_HEADROOM_KIB',
                'FREN_BUILD_FALLBACK_KIB', 'FREN_BUILD_TIMEOUT_MS'):
        env.pop(key, None)
    (work / 'lean-toolchain').write_text(pin + '\n')
    nested = work / 'caller'; nested.mkdir()
    def states():
        return set(work.glob('fren-build-*'))
    def invoke(label, command, *, extra=None, script=HEAVY, cancel=False):
        before = states()
        local = dict(env, **(extra or {}))
        ready = work / (label + '.pid'); local['READY'] = str(ready)
        argv = [str(script), '--offline', *map(str, command)]
        start = time.monotonic()
        p = subprocess.Popen(argv, cwd=nested, env=local, stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if cancel:
            deadline = start + 15
            while not ready.exists() and p.poll() is None and time.monotonic() < deadline:
                time.sleep(.02)
            assert ready.exists(), p.communicate(timeout=5)
            p.send_signal(signal.SIGTERM)
        try:
            out, err = p.communicate('input λ\n'.encode(), timeout=20)
        except subprocess.TimeoutExpired:
            p.terminate()
            out, err = p.communicate(timeout=10)
            raise AssertionError((label, 'timeout', out, err))
        elapsed = time.monotonic() - start
        new = sorted(states() - before)
        row = {'case': label, 'argv': argv, 'status': p.returncode,
               'wrapper_wall_seconds': elapsed, 'states': list(map(str, new))}
        for stream, data in (('stdout', out), ('stderr', err)):
            path = work / (label + '.' + stream); path.write_bytes(data)
            row[stream] = str(path)
        log = work / 'home/.cache/heavy/log.jsonl'
        if log.exists():
            row['heavy'] = json.loads(log.read_text().splitlines()[-1])
        results.append(row)
        (work / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        if ready.exists():
            pid = int(ready.read_text())
            try:
                os.kill(pid, 0)
                raise AssertionError((label, 'owned descendant survived', pid))
            except ProcessLookupError:
                pass
        return p.returncode, out, err, new
    # Baseline negative: old Heavy does not dispatch to the controller.
    baseline = work / 'old-heavy'
    baseline.write_bytes(subprocess.check_output(['git', 'show',
        'f7f319d0b1748cee8e521f6c032749edffc446c2:scripts/heavy'], cwd=ROOT))
    baseline.chmod(0o755)
    code, _, _, new = invoke('old-no-dispatch', [lake, 'build'],
                             extra={'CONTROL': 'assert-gated'}, script=baseline)
    assert code == 19 and not new
    code, _, _, new = invoke('new-dispatch', [lake, 'build'], extra={'CONTROL': 'assert-gated'})
    assert code == 0 and len(new) == 1
    code, out, err, new = invoke('literal-streams', [lake, '--no-cache', 'build', 'a b', '$x', 'λ'],
                                 extra={'STATUS': '7', 'CONTROL': 'pipes'})
    assert code == 7 and out.endswith(b'O' * 131072) and err.endswith(b'E' * 131072)
    data = json.loads(out.splitlines()[0])
    assert data['argv'] == ['--no-cache', 'build', 'a b', '$x', 'λ']
    assert data['cwd'] == str(nested) and data['sentinel'] == env['SENTINEL']
    assert data['stdin'] == 'input λ\n' and data['budget'] and data['sysroot']
    assert data['net'] != os.readlink('/proc/self/ns/net')
    assert new[0].stat().st_mode & 0o777 == 0o700
    assert (new[0] / 'requests.tsv').read_text() == ''
    # Dispatch must not select the script checkout's Lake or caller directory.
    code, out, _, _ = invoke('directory-operand', [lake, '-d', str(work), 'build', 'x'])
    assert code == 0 and json.loads(out)['argv'] == ['-d', str(work), 'build', 'x']
    code, _, _, _ = invoke('signal', [lake, 'build'], extra={'CONTROL': 'signal'})
    assert code == 143
    code, out, err, _ = invoke('missing-direct', [lake, 'env'], extra={'CONTROL': 'missing'})
    direct = (code, out, err)
    code, out, err, new = invoke('missing-gated', [lake, 'build'], extra={'CONTROL': 'missing'})
    assert code == direct[0] != 0 and out == direct[1]
    assert err.split(b'\n', 1)[1] == direct[2], (err, direct)
    rows = [json.loads(p.read_text()) for p in (new[0] / 'state/overlay/records').glob('process-*.json')]
    assert any(r['child_present'] and r['raw_wait_status'] != 0 and r['gate_errno'] == 0
               and r['request_provenance'] == 'explicit-unknown-fallback' for r in rows)
    for label, extra in (
        ('excess-allowance', {'FREN_BUILD_ALLOWANCE_KIB': '99999999'}),
        ('small-outer', {'HEAVY_MEM_GB': '.05'}),
        ('bad-headroom', {'FREN_BUILD_HEADROOM_KIB': '99999999'}),
        ('bad-fallback', {'FREN_BUILD_FALLBACK_KIB': '0'}),
        ('missing-requests', {'FREN_BUILD_REQUESTS_FILE': str(work / 'absent')}),
        ('already-budgeted', {'HEAVY_BUDGET_DIR': str(work / 'unowned')}),
        ('existing-overlay', {'LEAN_SYSROOT': str(work / 'unowned')})):
        code, _, _, _ = invoke(label, [lake, 'build'], extra=extra)
        assert code == 125, (label, code)
    manifest = work / 'requests'; manifest.write_text('bad\n')
    code, _, _, _ = invoke('malformed-requests', [lake, 'build'],
                           extra={'FREN_BUILD_REQUESTS_FILE': str(manifest)})
    assert code == 125
    # Explicit native Lake stays explicit even with an unrelated elan override.
    code, _, _, _ = invoke('explicit-lake', [lake, 'build'], extra={'ELAN_TOOLCHAIN': 'uninstalled-test-pin'})
    assert code == 0
    for label, prefix, extra in (
        ('missing-toolchain', ['lake'], {'ELAN_TOOLCHAIN': 'uninstalled-test-pin'}),
        ('plus-toolchain', ['lake', '+uninstalled-test-pin'], {})):
        code, _, err, new = invoke(label, [*prefix, 'build'], extra=extra)
        assert code == 125 and b'not installed' in err and not new
        assert b'download' not in err and b'could not check' not in err
    # Real elan shim discovery uses the parent caller pin, not -d's pin.
    selected_env = dict(env)
    selected_env.pop('ELAN_TOOLCHAIN', None)
    with mock.patch.dict(os.environ, selected_env, clear=True):
        old_cwd = Path.cwd()
        os.chdir(nested)
        try:
            selected, command = build.selected_lake(['lake', '+' + pin, 'build'], selected_env)
        finally:
            os.chdir(old_cwd)
    assert selected.resolve() == real and command == [str(real.parent / 'lake'), 'build']
    with mock.patch.dict(os.environ, env, clear=True):
        selected, command = build.selected_lake(['lake', '+v4.32.0', 'build'], dict(env))
    assert selected.resolve() == real and command == [str(real.parent / 'lake'), 'build']
    # Normal non-build and bootstrap argv retain their original invocation.
    for label, command in (('non-build', [lake, 'env', 'literal build']),
                           ('option-operand', [lake, '-K', 'build', 'env']),
                           ('bootstrap', [lake, '-d', str(ROOT / 'tools/heavy-observe'), 'build', 'budget_session'])):
        code, out, _, new = invoke(label, command)
        assert code == 0 and not new and json.loads(out)['budget'] is None
    missing = work / 'missing/scripts'; missing.mkdir(parents=True)
    for name in ('heavy', 'fren-build', 'heavy-lean-build'):
        dest = missing / name; dest.write_bytes((ROOT / 'scripts' / name).read_bytes()); dest.chmod(0o755)
    code, _, err, new = invoke('missing-tools', [lake, 'build'], script=missing / 'heavy')
    assert code == 125 and b'missing prebuilt' in err and not new
    # Actual recursive overlay rejection, before any compiler can exec itself.
    recursive = work / 'recursive'; recursive.mkdir()
    recursive_lake = recursive / 'lake'
    recursive_lake.write_bytes(lake.read_bytes()); recursive_lake.chmod(0o755)
    (recursive / 'lean').symlink_to(ROOT / 'tools/heavy-observe/.lake/build/bin/heavy_observe')
    code, _, err, _ = invoke('recursive-compiler', [recursive_lake, 'build'])
    assert code == 125 and b'recursive overlay' in err
    (recursive / 'lean').unlink()
    code, _, err, new = invoke('missing-compiler', [recursive_lake, 'build'])
    assert code == 125 and b'missing compiler' in err and not new
    code, _, _, _ = invoke('cancellation', [lake, 'build'], extra={'CONTROL': 'wait'}, cancel=True)
    assert code == 125  # The controller retains wait status 15 and reports cancellation.
    assert b'cleanup errno=0; command wait status=15' in (work / 'cancellation.stderr').read_bytes()
    code, _, err, _ = invoke('outer-backstop', [lake, 'build'], extra={
        'CONTROL': 'memory', 'HEAVY_MEM_GB': '.2', 'FREN_BUILD_HEADROOM_KIB': '1000',
        'FREN_BUILD_FALLBACK_KIB': '1000'})
    assert code == 137 and b'heavy: killed' in err
    row = results[-1]['heavy']
    assert row['compiler_budget'] and row['peak_rss_kb'] > int(.2 * 1024 * 1024)
    code, _, err, new = invoke('already-budgeted-explicit', [ROOT / 'scripts/heavy-lean-build',
        '--state', str(work / 'must-not-exist'), '--real-lean', real,
        '--allowance-kib', '1300000', '--headroom-kib', '100000',
        '--fallback-kib', '600000', '--timeout-ms', '30000',
        '--requests', manifest, '--', lake, 'build'],
        extra={'HEAVY_BUDGET_DIR': str(work / 'unowned')})
    assert code == 125 and b'already budgeted' in err and not new
    assert not (work / 'must-not-exist').exists()
    # Registry leases must all have been released, including failed/cancelled calls.
    assert heavy.jobs(str(work / 'home/.cache/heavy')) == []
    summary = {'cases': len(results), 'status': 'passed', 'real_lean': str(real),
               'compiler_sha256': hashlib.sha256(real.read_bytes()).hexdigest(),
               'results': str(work / 'results.json')}
    (work / 'report.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
