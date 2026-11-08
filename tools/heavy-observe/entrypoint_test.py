#!/usr/bin/env python3
"""Bounded actual-entrypoint controls; requires prebuilt standalone tools."""
import hashlib
import json
import os
import re
import resource
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
ENTRY = ROOT / 'scripts/heavy-lean-build'
BUILD = ROOT / 'scripts/fren-build'
TOOLS = ROOT / 'tools/heavy-observe/.lake/build/bin'


def cpu_controls(work, pkg, env, request, results):
    # Limit the actual owned compiler, not the session or metadata queries.
    fixture = work / 'fixture/bin/lean'; fixture.parent.mkdir(parents=True)
    source = work / 'fixture.c'
    source.write_text(r'''#include <string.h>
#include <unistd.h>
#include <stdio.h>
int main(int n, char **v) {
    if (n > 1 && !strcmp(v[1], "--print-prefix")) { char p[4096]; ssize_t k = readlink("/proc/self/exe", p, sizeof(p)-1); if (k < 9) return 1; p[k-9] = 0; puts(p); return 0; }
    if (n > 1 && (!strcmp(v[1], "--version") || !strcmp(v[1], "--githash"))) return 0;
    if (n > 1 && !strcmp(v[1], "burn.lean")) { volatile unsigned long x = 1; for (;;) x++; }
    write(1, "fixture ok\n", 11); return 0;
}
''')
    subprocess.run(['cc', '-O2', str(source), '-o', str(fixture)], check=True)
    def limited(label, setting, arg, lower_hard=False):
        state = work / label
        test_env = env.copy()
        if setting is not None: test_env['HEAVY_COMPILER_CPU_SECONDS'] = setting
        else: test_env.pop('HEAVY_COMPILER_CPU_SECONDS', None)
        command = [str(ENTRY), '--state', str(state), '--real-lean', str(fixture),
                   '--allowance-kib', '1300000', '--headroom-kib', '100000',
                   '--fallback-kib', '600000', '--timeout-ms', '30000', '--requests', str(request),
                   '--', sys.executable, '-c',
                   'import os,subprocess,sys; p=subprocess.run([os.environ["LEAN_SYSROOT"]+"/bin/lean",sys.argv[1]]); sys.exit(128-p.returncode if p.returncode<0 else p.returncode)', arg]
        p = subprocess.run(command, cwd=pkg, env=test_env, capture_output=True, timeout=10,
                           preexec_fn=(lambda: resource.setrlimit(resource.RLIMIT_CPU, (1, 1))) if lower_hard else None)
        records = list((state / 'overlay/records').glob('process-*.json'))
        rows = [json.loads(f.read_text()) for f in records]
        results.append(dict(case=label, status=p.returncode, stderr=p.stderr.decode(), records=rows))
        return p, rows
    p, rows = limited('cpu-positive', '1', 'ok.lean')
    assert p.returncode == 0 and rows[0]['compiler_cpu_limit_seconds'] == 1 and rows[0]['raw_wait_status'] == 0
    p, rows = limited('cpu-negative', '1', 'burn.lean')
    assert p.returncode == 137 and rows[0]['compiler_cpu_limit_seconds'] == 1
    assert rows[0]['result_kind'] == 1 and rows[0]['result_detail'] == 9 and rows[0]['raw_wait_status'] == 9
    p, rows = limited('cpu-default', None, 'ok.lean')
    assert p.returncode == 0 and rows[0]['compiler_cpu_limit_seconds'] is None
    for bad in ('0', '-1', 'abc', '2147483648', ''):
        p, rows = limited('cpu-invalid-' + (bad or 'empty'), bad, 'ok.lean')
        assert p.returncode == 125 and not rows
    p, rows = limited('cpu-setup-failure', '2', 'ok.lean', lower_hard=True)
    assert p.returncode == 125 and rows[0]['launch_errno'] != 0
    assert rows[0]['compiler_cpu_limit_seconds'] is None and rows[0]['result_kind'] == 3
    direct_env = env.copy(); direct_env.pop('HEAVY_BUDGET_DIR', None)
    direct_env['HEAVY_COMPILER_CPU_SECONDS'] = '1'
    p = subprocess.run([str(work / 'cpu-positive/overlay/bin/lean'), 'ok.lean'], cwd=pkg,
                       env=direct_env, capture_output=True, timeout=5)
    assert p.returncode == 125
    p, rows = limited('cpu-query', '1', '--version')
    assert p.returncode == 0 and rows[0]['compiler_cpu_limit_seconds'] is None

def main():
    real = Path(os.environ.get('HEAVY_TEST_REAL_LEAN') or
                (subprocess.check_output(['lean', '--print-prefix'], text=True).strip() + '/bin/lean')).resolve(strict=True)
    lake = real.parent / 'lake'
    parent = Path(os.environ.get('HEAVY_ENTRYPOINT_TEST_DIR', tempfile.gettempdir())).resolve()
    work = Path(tempfile.mkdtemp(prefix='heavy-entrypoint-', dir=parent))
    pkg = work / 'pkg'; pkg.mkdir()
    (pkg / 'lakefile.toml').write_text('name = "entrypoint_test"\nenableArtifactCache = false\n[[lean_lib]]\nname = "Tiny"\n')
    (pkg / 'lean-toolchain').write_text((ROOT / 'lean-toolchain').read_text())
    (pkg / 'Tiny').mkdir()
    basic = pkg / 'Tiny/Basic.lean'; basic.write_text('import Std\ndef tiny : Nat := 42\n')
    (pkg / 'Tiny.lean').write_text('import Tiny.Basic\ndef nextTiny : Nat := tiny + 1\n')
    value = subprocess.check_output([str(TOOLS / 'process_tests'), '--read', str(basic)], text=True).strip()
    assert value.startswith('some:')
    request = work / 'requests'
    request.write_text(f'{basic}\tlean-bytearray64:{basic.stat().st_size}:{value[5:]}\t500000\n')
    env = os.environ.copy(); env['LAKE_CACHE_DIR'] = str(work / 'cache'); env['ENTRY_SENTINEL'] = 'spaces λ $ literal'
    results = []
    def call(label, command, *, req=request, extra=None, entry=ENTRY):
        state = work / label
        argv = [str(entry), '--state', str(state), '--real-lean', str(real), '--allowance-kib', '1300000',
                '--headroom-kib', '100000', '--fallback-kib', '600000', '--timeout-ms', '30000',
                '--requests', str(req), '--', *map(str, command)]
        p = subprocess.run(argv, cwd=pkg, env=env, capture_output=True, timeout=20)
        results.append({'case': label, 'argv': argv, 'status': p.returncode,
                        'stdout': p.stdout.decode(errors='replace'), 'stderr': p.stderr.decode(errors='replace')})
        return p, state
    p, state = call('argv', [sys.executable, '-c', 'import os,sys,json; print(json.dumps([sys.argv[1:],os.environ["ENTRY_SENTINEL"]])); sys.exit(7)', 'space value', '$literal', 'λ'])
    assert p.returncode == 7 and json.loads(p.stdout) == [['space value', '$literal', 'λ'], env['ENTRY_SENTINEL']]
    p, _ = call('signal', [sys.executable, '-c', 'import os,signal; os.kill(os.getpid(), signal.SIGTERM)'])
    assert p.returncode == 143
    p, state = call('lake', [lake, '--no-cache', '--verbose', 'build', '+Tiny'])
    assert p.returncode == 0, p.stderr
    rows = [json.loads(p.read_text()) for p in (state / 'overlay/records').glob('process-*.json')]
    compiled = [x for x in rows if x['input_kind'] == 'file']
    assert len(compiled) == 2
    by_source = {x['source']: x for x in compiled}
    assert by_source[str(basic)]['request_provenance'] == 'explicit-source-request'
    assert by_source[str(basic)]['requested_reservation_kib'] == 500000
    assert by_source[str(pkg / 'Tiny.lean')]['request_provenance'] == 'explicit-unknown-fallback'
    assert by_source[str(pkg / 'Tiny.lean')]['requested_reservation_kib'] == 600000
    assert all(x['child_present'] and x['raw_wait_status'] == 0 and x['gate_errno'] == 0 for x in compiled)
    cpu_controls(work, pkg, env, request, results)
    env['HEAVY_COMPILER_CPU_SECONDS'] = '10'
    # The ordinary command builds in the caller's package and retains an empty
    # manifest and fallback records in a private directory chosen under TMPDIR.
    env['TMPDIR'] = str(work)
    env['FREN_BUILD_FALLBACK_KIB'] = '550000'
    basic.write_text(basic.read_text() + '-- rebuild\n')
    p = subprocess.run([str(BUILD), '+Tiny'], cwd=pkg, env=env, capture_output=True, timeout=30)
    assert p.returncode == 0, p.stderr
    builds = list(work.glob('fren-build-*'))
    assert len(builds) == 1 and builds[0].stat().st_mode & 0o777 == 0o700
    assert (builds[0] / 'requests.tsv').read_text() == ''
    built = [json.loads(f.read_text()) for f in (builds[0] / 'state/overlay/records').glob('process-*.json')]
    assert all(x['real_compiler'] == str(real) and x['cwd'] == str(pkg) for x in built)
    assert all(x['compiler_cpu_limit_seconds'] == 10 for x in built if x['input_kind'] == 'file')
    assert any(x['input_kind'] == 'file' and x['source'] == str(basic)
               and x['request_provenance'] == 'explicit-unknown-fallback'
               and x['requested_reservation_kib'] == 550000 for x in built)
    # Real short-command source requests, including a stale fingerprint on rebuild.
    other = pkg / 'Tiny.lean'
    def fingerprint(path):
        value = subprocess.check_output([str(TOOLS / 'process_tests'), '--read', str(path)], text=True).strip()
        assert value.startswith('some:')
        return f'lean-bytearray64:{path.stat().st_size}:{value[5:]}'
    request.write_text(f'{basic}\t{fingerprint(basic)}\t410000\n'
                       f'{other}\t{fingerprint(other)}\t470000\n')
    env['FREN_BUILD_REQUESTS_FILE'] = str(request)
    short = Path(os.environ.get('HEAVY_TEST_SHORT_BUILD', str(BUILD)))
    old = os.environ.get('HEAVY_TEST_OLD_SHORT') == '1'
    def short_build(label):
        shutil.rmtree(pkg / '.lake', ignore_errors=True)
        before = set(work.glob('fren-build-*'))
        proc = subprocess.run([str(short), '+Tiny'], cwd=pkg, env=env, capture_output=True, timeout=30)
        assert proc.returncode == 0, proc.stderr
        created = set(work.glob('fren-build-*')) - before
        assert len(created) == 1
        directory = created.pop()
        records = [json.loads(f.read_text()) for f in (directory / 'state/overlay/records').glob('process-*.json')]
        files = {x['source']: x for x in records if x['input_kind'] == 'file'}
        assert set(files) == {str(basic), str(other)}
        assert all(x['schema'] == 3 and x['child_present'] and x['raw_wait_status'] == 0
                   and x['gate_errno'] == 0 and x['cwd'] == str(pkg) for x in files.values())
        artifacts = {str(f.relative_to(pkg / '.lake/build')): hashlib.sha256(f.read_bytes()).hexdigest()
                     for f in (pkg / '.lake/build').rglob('*.olean')}
        results.append({'case': label, 'status': proc.returncode, 'stdout': proc.stdout.decode(),
                        'stderr': proc.stderr.decode(), 'records': files, 'artifacts': artifacts})
        return files, artifacts
    baseline = os.environ.get('HEAVY_TEST_BASELINE_SHORT')
    if baseline:
        current_short = short
        short = Path(baseline)
        baseline_files, baseline_artifacts = short_build('baseline-explicit-requests')
        baseline_result = results[-1]
        assert all(row['request_provenance'] == 'explicit-unknown-fallback'
                   and row['requested_reservation_kib'] == 550000 for row in baseline_files.values())
        short = current_short
    files, artifacts = short_build('explicit-requests')
    if baseline:
        assert artifacts == baseline_artifacts
        assert results[-1]['status'] == baseline_result['status']
        def normalize(stream):
            return re.sub(r'\([0-9.]+(?:ms|s)\)', '(TIME)', re.sub(r'fren-build-[^/\s]+', 'fren-build-STATE', stream))
        assert normalize(results[-1]['stdout']) == normalize(baseline_result['stdout']), (results[-1]['stdout'], baseline_result['stdout'])
        assert normalize(results[-1]['stderr']) == normalize(baseline_result['stderr'])

    for source, demand in ((basic, 410000), (other, 470000)):
        row = files[str(source)]
        assert row['request_provenance'] == ('explicit-unknown-fallback' if old else 'explicit-source-request')
        assert row['requested_reservation_kib'] == (550000 if old else demand)
    basic.write_text(basic.read_text() + '-- changed after manifest\n')
    files, _ = short_build('stale-request')
    assert files[str(basic)]['request_provenance'] == 'explicit-unknown-fallback'
    assert files[str(basic)]['requested_reservation_kib'] == 550000
    if not old:
        assert files[str(other)]['request_provenance'] == 'explicit-source-request'
        assert files[str(other)]['requested_reservation_kib'] == 470000
        # Invalid configuration must not start Lake or create a retained session.
        unreadable = work / 'unreadable'; unreadable.write_text(''); unreadable.chmod(0)
        for invalid in ('', 'relative', str(work / 'absent'), str(work), str(unreadable)):
            before = set(work.glob('fren-build-*'))
            invalid_env = dict(env, FREN_BUILD_REQUESTS_FILE=invalid)
            proc = subprocess.run([str(BUILD), '+Tiny'], cwd=pkg, env=invalid_env, capture_output=True, timeout=10)
            assert proc.returncode == 125 and b'FREN_BUILD_REQUESTS_FILE' in proc.stderr, (invalid, proc.returncode, proc.stderr)
            assert set(work.glob('fren-build-*')) == before
        fifo = work / 'stable-fifo'; os.mkfifo(fifo)
        before = set(work.glob('fren-build-*'))
        proc = subprocess.run([str(BUILD), '+Tiny'], cwd=pkg,
                              env=dict(env, FREN_BUILD_REQUESTS_FILE=str(fifo)), capture_output=True, timeout=10)
        assert proc.returncode == 125 and set(work.glob('fren-build-*')) == before
        # Replace a regular manifest immediately at either implementation's actual
        # open boundary, so the old and new controls exercise the same transition.
        hook = r"""
import os, pathlib, runpy, sys
path = os.environ['FREN_BUILD_REQUESTS_FILE']
marker = os.environ['FIFO_MARKER']
original_path_open = pathlib.Path.open
original_os_open = os.open
replaced = False
def replace(candidate):
    global replaced
    if not replaced and os.fspath(candidate) == path:
        os.unlink(path)
        os.mkfifo(path)
        pathlib.Path(marker).write_text('replaced at open')
        replaced = True
def path_open(self, *args, **kwargs):
    replace(self)
    return original_path_open(self, *args, **kwargs)
def os_open(candidate, *args, **kwargs):
    replace(candidate)
    return original_os_open(candidate, *args, **kwargs)
pathlib.Path.open = path_open
os.open = os_open
script = sys.argv[1]
sys.argv = [script, '+Tiny']
runpy.run_path(script, run_name='__main__')
"""
        def transition(script, label, expect_timeout):
            target = work / (label + '-manifest'); target.write_text('')
            marker = work / (label + '-marker')
            before = set(work.glob('fren-build-*'))
            transition_env = dict(env, FREN_BUILD_REQUESTS_FILE=str(target), FIFO_MARKER=str(marker))
            try:
                proc = subprocess.run([sys.executable, '-c', hook, str(script)], cwd=pkg,
                                      env=transition_env, capture_output=True, timeout=5)
                result = {'case': label, 'status': proc.returncode, 'stdout': proc.stdout.decode(),
                          'stderr': proc.stderr.decode(), 'timed_out': False}
                assert not expect_timeout and proc.returncode == 125 and b'FREN_BUILD_REQUESTS_FILE' in proc.stderr
            except subprocess.TimeoutExpired as error:
                result = {'case': label, 'timed_out': True, 'stdout': (error.stdout or b'').decode(),
                          'stderr': (error.stderr or b'').decode()}
                assert expect_timeout
            finally:
                target.unlink(missing_ok=True)
            assert marker.read_text() == 'replaced at open'
            assert set(work.glob('fren-build-*')) == before
            results.append(result)
        old_transition = os.environ.get('HEAVY_TEST_OLD_TRANSITION_BUILD')
        if old_transition:
            transition(old_transition, 'old-fifo-transition', True)
        transition(BUILD, 'fifo-transition', False)
        bad = work / 'bad-short'; bad.write_text('invalid\n')
        proc = subprocess.run([str(BUILD), '+Tiny'], cwd=pkg,
                              env=dict(env, FREN_BUILD_REQUESTS_FILE=str(bad)), capture_output=True, timeout=10)
        assert proc.returncode == 125
    del env['FREN_BUILD_REQUESTS_FILE']
    p = subprocess.run([str(BUILD), 'missing target $literal'], cwd=pkg, env=env, capture_output=True, timeout=30)
    assert p.returncode != 0 and b'missing target $literal' in p.stderr + p.stdout
    env['FREN_BUILD_FALLBACK_KIB'] = '0'
    p = subprocess.run([str(BUILD), '+Tiny'], cwd=pkg, env=env, capture_output=True, timeout=10)
    assert p.returncode == 125
    (pkg / 'lean-toolchain').write_text('not-an-installed-toolchain\n')
    p = subprocess.run([str(BUILD), '+Tiny'], cwd=pkg, env=env, capture_output=True, timeout=10)
    assert p.returncode == 125 and b'not installed' in p.stderr
    missing = work / 'missing-build/scripts'; missing.mkdir(parents=True)
    shutil.copy2(BUILD, missing / 'fren-build')
    p = subprocess.run([str(missing / 'fren-build'), '+Tiny'], cwd=pkg, env=env, capture_output=True)
    assert p.returncode == 125 and b'scripts/heavy lake -d tools/heavy-observe build heavy_observe budget_session --wfail' in p.stderr
    bad = work / 'bad'; bad.write_text('invalid\n')
    p, _ = call('bad-manifest', [sys.executable, '-c', 'raise SystemExit(0)'], req=bad)
    assert p.returncode == 125
    p = subprocess.run([str(ENTRY), '--state', 'relative'], capture_output=True)
    results.append({'case': 'malformed-cli', 'status': p.returncode, 'stderr': p.stderr.decode()})
    assert p.returncode != 0
    fake = work / 'missing/scripts'; fake.mkdir(parents=True); shutil.copy2(ENTRY, fake / 'heavy-lean-build')
    p, _ = call('missing-tools', [sys.executable, '-c', 'pass'], entry=fake / 'heavy-lean-build')
    assert p.returncode == 125 and b'missing prebuilt' in p.stderr
    (work / 'result.json').write_text(json.dumps({'cases': results, 'real_lean': str(real),
        'real_lean_sha256': hashlib.sha256(real.read_bytes()).hexdigest(), 'lake': str(lake),
        'compiler_records': rows}, indent=2) + '\n')
    print(f'entrypoint controls passed: {work}')


if __name__ == '__main__':
    main()
