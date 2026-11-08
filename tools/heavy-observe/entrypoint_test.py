#!/usr/bin/env python3
"""Bounded actual-entrypoint controls; requires prebuilt standalone tools."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
ENTRY = ROOT / 'scripts/heavy-lean-build'
BUILD = ROOT / 'scripts/fren-build'
TOOLS = ROOT / 'tools/heavy-observe/.lake/build/bin'


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
    assert any(x['input_kind'] == 'file' and x['source'] == str(basic)
               and x['request_provenance'] == 'explicit-unknown-fallback'
               and x['requested_reservation_kib'] == 550000 for x in built)
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
