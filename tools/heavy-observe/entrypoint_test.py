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
TOOLS = ROOT / 'tools/heavy-observe/.lake/build/bin'


def main():
    real = Path(os.environ.get('HEAVY_TEST_REAL_LEAN') or
                (subprocess.check_output(['lean', '--print-prefix'], text=True).strip() + '/bin/lean')).resolve(strict=True)
    lake = real.parent / 'lake'
    parent = Path(os.environ.get('HEAVY_ENTRYPOINT_TEST_DIR', tempfile.gettempdir())).resolve()
    work = Path(tempfile.mkdtemp(prefix='heavy-entrypoint-', dir=parent))
    pkg = work / 'pkg'; pkg.mkdir()
    (pkg / 'lakefile.toml').write_text('name = "entrypoint_test"\nenableArtifactCache = false\n[[lean_lib]]\nname = "Tiny"\n')
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
