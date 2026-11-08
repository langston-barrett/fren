#!/usr/bin/env python3
"""Actual gated observer feedback, using the owned compiler fixture."""
import json
import os
import signal
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from overlay import create
BIN = HERE / '.lake/build/bin'

if sys.argv[1:2] == ['--producer']:
    work, shim = map(Path, sys.argv[2:])
    os.environ['BUDGET_EVENTS'] = str(work / 'events')
    results = {}
    for name, args, closed in [('small', ['Small.lean'], False), ('large', ['Large.lean'], False),
                               ('failure', ['Exit.lean'], False), ('signal', ['Signal.lean'], False), ('unknown', ['Unknown.lean', '--unsupported'], False),
                               ('query', ['--githash'], False), ('closed', ['Closed.lean'], True)]:
        args = [str(work / x) if x.endswith('.lean') else x for x in args]
        if closed:
            read, write = os.pipe(); os.close(read)
            p = subprocess.run([str(shim), *args], stdout=subprocess.PIPE, stderr=write, timeout=5)
            os.close(write); err = ''
        else:
            p = subprocess.run([str(shim), *args], capture_output=True, timeout=5)
            err = p.stderr.decode()
        results[name] = {'status': p.returncode, 'stdout': p.stdout.decode(), 'stderr': err}
    env = dict(os.environ); env.pop('HEAVY_BUDGET_DIR', None)
    p = subprocess.run([str(shim), str(work / 'Small.lean')], env=env, capture_output=True, timeout=5)
    results['nocharge'] = {'status': p.returncode, 'stdout': p.stdout.decode(), 'stderr': p.stderr.decode()}
    (work / 'results.json').write_text(json.dumps(results))
    sys.exit(0)

with tempfile.TemporaryDirectory(prefix='heavy-feedback-') as tmp:
    work = Path(tmp); (work / 'events').mkdir()
    real = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip()) / 'bin/lean'
    overlay = create(work / 'overlay', real, Path(os.environ.get('HEAVY_TEST_OBSERVER', str(BIN / 'heavy_observe'))))
    fixture = work / 'fixture'; fixture.write_bytes((HERE / 'budget_fixture.py').read_bytes()); fixture.chmod(0o700)
    (overlay / 'real-lean.path').write_text(str(fixture))
    lines = []
    for name, demand in [('Small', 1), ('Large', 1000000), ('Exit', 1), ('Signal', 1), ('Unknown', 1), ('Closed', 1)]:
        source = work / (name + '.lean'); source.write_text('fixture')
        (work / 'events' / (name + '.release')).touch()
        digest = subprocess.check_output([str(BIN / 'process_tests'), '--read', str(source)], text=True).strip().removeprefix('some:')
        lines.append(f'{source}\tlean-bytearray64:{source.stat().st_size}:{digest}\t{demand}\n')
    manifest = work / 'manifest'; manifest.write_text(''.join(lines))
    cmd = [str(BIN / 'budget_session'), str(work / 'session'), '2000000', '1', '1', '2500', str(manifest), '--',
           sys.executable, '-I', __file__, '--producer', str(work), str(overlay / 'bin/lean')]
    p = subprocess.run(cmd, capture_output=True, timeout=20)
    assert p.returncode == 0, (p.stdout, p.stderr)
    results = json.loads((work / 'results.json').read_text())
    rows = [json.loads(p.read_text()) for p in (overlay / 'records').glob('process-*.json')]
    by_source = {Path(r['source']).stem: r for r in rows if r['source'] and 'gate_errno' in r}
    for name, key, status in [('small', 'Small', 0), ('failure', 'Exit', 7), ('signal', 'Signal', -signal.SIGTERM), ('closed', 'Closed', 0)]:
        row = by_source[key]; peak = row['measured_peak_rss_kib']; request = row['requested_reservation_kib']
        assert peak > request > 0 and results[name]['status'] == status
        assert results[name]['stdout'] == f'stdout {key}\n'
        if name != 'closed' and os.environ.get('HEAVY_NOTICE_FAULT') not in ('EBADF', 'ENOSPC'):
            assert f'observed child peak {peak} KiB above requested amount {request} KiB by {peak-request} KiB' in results[name]['stderr']
        if name != 'closed':
            assert f'stderr {key}\n' in results[name]['stderr']
    row = by_source['Large']; assert row['measured_peak_rss_kib'] <= row['requested_reservation_kib']
    for name in ['large', 'unknown', 'query', 'nocharge']:
        assert results[name]['status'] == 0 and 'observed child peak' not in results[name]['stderr']
    assert results['query']['stdout'] == 'synthetic-request-fixture\n'
    assert any(r['input_kind'] == 'unknown' for r in rows)
    print(json.dumps({'passed': True, 'results': results, 'records': rows}, indent=2))
