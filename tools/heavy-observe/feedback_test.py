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
    # Same silent exit-7 child with a full open pipe and with a closed pipe.
    # The full pipe is never drained before the observer returns.
    for mode in ('full', 'closed'):
        read, write = os.pipe()
        filled = 0
        if mode == 'full':
            os.set_blocking(write, False)
            while True:
                try: filled += os.write(write, b'x' * 4096)
                except BlockingIOError: break
            os.set_blocking(write, True)
            assert filled > 0
        else:
            os.close(read)
        p = subprocess.Popen([str(shim), str(work / 'Silent.lean')], stdout=subprocess.PIPE, stderr=write)
        os.close(write)
        try:
            stdout, _ = p.communicate(timeout=5)
            if mode == 'full':
                chunks = []
                while chunk := os.read(read, 65536): chunks.append(chunk)
                assert b''.join(chunks) == b'x' * filled
            results['silent-' + mode] = {'status': p.returncode, 'stdout': stdout.decode(), 'filled': filled,
                                         'returned_before_drain': mode == 'full'}
        finally:
            if p.poll() is None:
                p.kill(); p.communicate()
            if mode == 'full': os.close(read)
    env = dict(os.environ); env.pop('HEAVY_BUDGET_DIR', None)
    p = subprocess.run([str(shim), str(work / 'Small.lean')], env=env, capture_output=True, timeout=5)
    results['nocharge'] = {'status': p.returncode, 'stdout': p.stdout.decode(), 'stderr': p.stderr.decode()}
    (work / 'results.json').write_text(json.dumps(results))
    sys.exit(0)

with tempfile.TemporaryDirectory(prefix='heavy-feedback-') as tmp:
    work = Path(tmp); (work / 'events').mkdir()
    real = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip()) / 'bin/lean'
    overlay = create(work / 'overlay', real, BIN / 'heavy_observe')
    fixture = work / 'fixture'; fixture.write_bytes((HERE / 'budget_fixture.py').read_bytes()); fixture.chmod(0o700)
    (overlay / 'real-lean.path').write_text(str(fixture))
    lines = []
    for name, demand in [('Small', 1), ('Large', 1000000), ('Exit', 1), ('Signal', 1), ('Unknown', 1), ('Closed', 1), ('Silent', 1)]:
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
    by_source = {Path(r['source']).stem: r for r in rows if r['source'] and 'gate_errno' in r and not r['source'].endswith('Silent.lean')}
    for name, key, status in [('small', 'Small', 0), ('failure', 'Exit', 7), ('signal', 'Signal', -signal.SIGTERM), ('closed', 'Closed', 0)]:
        row = by_source[key]; peak = row['measured_peak_rss_kib']; request = row['requested_reservation_kib']
        assert peak > request > 0 and row['request_excess_kib'] == peak - request
        assert results[name]['status'] == status and results[name]['stdout'] == f'stdout {key}\n'
        if name != 'closed': assert results[name]['stderr'] == f'stderr {key}\n'
    row = by_source['Large']; assert row['measured_peak_rss_kib'] <= row['requested_reservation_kib']
    assert row['request_excess_kib'] == 0
    for name in ['large', 'unknown', 'query', 'nocharge']:
        assert results[name]['status'] == 0
    assert results['query']['stdout'] == 'synthetic-request-fixture\n'
    assert results['nocharge']['stderr'] == 'stderr Small\n'
    unknown, = [r for r in rows if r['input_kind'] == 'unknown']
    query, = [r for r in rows if r['input_kind'] == 'query']
    nocharge, = [r for r in rows if r.get('schema') == 2 and r['input_kind'] == 'file']
    assert all(r['request_excess_kib'] is None for r in (unknown, query, nocharge))
    silent = [r for r in rows if (r.get('source') or '').endswith('Silent.lean')]
    assert len(silent) == 2
    for row in silent:
        assert row['shell_code'] == 7 and row['measured_peak_rss_kib'] > row['requested_reservation_kib'] > 0
        assert row['request_excess_kib'] == row['measured_peak_rss_kib'] - row['requested_reservation_kib']
    for name in ('silent-full', 'silent-closed'):
        assert results[name]['status'] == 7 and results[name]['stdout'] == ''
    assert results['silent-full']['filled'] > 0
    print(json.dumps({'passed': True, 'results': results, 'records': rows}, indent=2))
