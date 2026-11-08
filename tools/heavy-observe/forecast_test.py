#!/usr/bin/env python3
"""Bounded actual-producer/JSON-mutation tests of the real Lean adviser.
Build compiler_advice and heavy_observe first; run through Heavy offline.
"""
import argparse
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from overlay import create


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    if args.output:
        work = args.output.absolute()
        work.mkdir(parents=True, exist_ok=False)
    else:
        (HERE / 'test-work').mkdir(exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix='forecast-', dir=HERE / 'test-work'))
    real = Path(os.environ.get('HEAVY_TEST_REAL_LEAN') or
                subprocess.check_output(['lean', '--print-prefix'], text=True).strip() + '/bin/lean').resolve(strict=True)
    overlay = create(work / 'overlay', real, HERE / '.lake/build/bin/heavy_observe')
    source = work / 'Tiny.lean'
    source.write_text('def tiny : Nat := 4\n')
    setup = work / 'setup.json'
    setup.write_text(json.dumps(dict(name='Tiny', isModule=False, plugins=[], dynlibs=[], options={}, importArts={})))
    compiler_args = ['Tiny.lean', '--setup', 'setup.json']
    env = dict(os.environ)
    for key in ('HEAVY_BUDGET_DIR', 'LEAN_SYSROOT', 'LAKE_OVERRIDE_LEAN', 'HEAVY_OBSERVE_DIR'):
        env.pop(key, None)
    # The only actual fixture compilation; subsequent calls only query identity.
    child = subprocess.run([str(overlay / 'bin/lean'), *compiler_args], cwd=work,
                           env=env, capture_output=True, timeout=5)
    assert child.returncode == 0, child.stderr
    record_path, = (overlay / 'records').glob('process-*.json')
    raw = json.loads(record_path.read_text())
    assert raw['boot_id'] == Path('/proc/sys/kernel/random/boot_id').read_text().strip()
    assert raw['identity_complete'] is False and raw['input_closure'] is None
    assert raw['raw_wait_status'] == 0 and raw['measured_peak_rss_kib'] > 0
    request = dict(real_compiler=str(real), args=compiler_args, cutoff_monotonic_ns=0,
                   recent_count=4, minimum_samples=1, records=[str(record_path)])
    evidence = []

    def invoke(name, rows=None, req=None, cwd=work, expected=None, samples=None, rejected=None):
        config = copy.deepcopy(request if req is None else req)
        case = work / name
        case.mkdir()
        if rows is not None:
            config['records'] = []
            for i, row in enumerate(rows):
                path = case / f'raw-{i}.json'
                path.write_text(json.dumps(row) if not isinstance(row, str) else row)
                config['records'].append(str(path))
        path = case / 'request.json'
        path.write_text(json.dumps(config))
        before = time.monotonic()
        p = subprocess.run([str(HERE / '.lake/build/bin/compiler_advice'), str(path)],
                           cwd=cwd, env=env, capture_output=True, text=True, timeout=5)
        assert p.returncode == 0, (name, p.stderr)
        result = json.loads(p.stdout)
        (case / 'advice.json').write_text(json.dumps(result, indent=2) + '\n')
        assert result['estimated_peak_rss_kib'] == expected, (name, result)
        assert result['status'] == ('unknown' if expected is None else 'estimate'), (name, result)
        if samples is not None:
            assert result['sample_count'] == samples, (name, result)
        if rejected is not None:
            assert result['rejected_records'] == rejected, (name, result)
        evidence.append(dict(case=name, elapsed_seconds=time.monotonic()-before, result=result))
        return result

    invoke('actual-record', expected=raw['measured_peak_rss_kib'], samples=1, rejected=0)
    def export(name, config=request, padding='123', cwd=work, ok=False, peak=None):
        case = work / ('export-' + name); case.mkdir()
        path = case / 'request.json'; path.write_text(json.dumps(config))
        proc = subprocess.run([str(HERE / '.lake/build/bin/compiler_advice'), '--manifest',
                               '--padding-kib', padding, str(path)], cwd=cwd, env=env,
                              capture_output=True, text=True, timeout=5)
        (case / 'stdout').write_text(proc.stdout); (case / 'stderr').write_text(proc.stderr)
        if ok:
            assert proc.returncode == 0 and proc.stderr == '', (name, proc.stderr)
            assert proc.stdout == f"{source.resolve()}\t{raw['source_before']}\t{(raw['peak_rss_kib'] if peak is None else peak) + int(padding)}\n"
        else:
            assert proc.returncode != 0 and proc.stdout == '' and proc.stderr, (name, proc)
        return proc

    export('actual-relative-source', ok=True)
    export('zero-padding', padding='0')
    export('negative-padding', padding='-1')
    export('fractional-padding', padding='1.5')
    export('huge-padding', padding=str(2**50))
    export('unknown', {**request, 'minimum_samples': 2})
    export('missing-record', {**request, 'records': [str(work / 'missing')]})
    bad = work / 'bad.json'; bad.write_text('{')
    export('malformed-record', {**request, 'records': [str(bad)]})
    export('stale-window', {**request, 'cutoff_monotonic_ns': raw['end_monotonic_ns'] + 1})
    boundary = work / 'boundary.json'
    boundary.write_text(json.dumps({**raw, 'peak_rss_kib': 2**50 - 1,
                                    'measured_peak_rss_kib': 2**50 - 1}))
    export('maximum-demand', {**request, 'records': [str(boundary)]}, padding='1',
           ok=True, peak=2**50 - 1)
    export('overflow-demand', {**request, 'records': [str(boundary)]}, padding='2')
    unsupported = work / 'tab\tproject'; unsupported.mkdir()
    (unsupported / source.name).write_bytes(source.read_bytes())
    (unsupported / setup.name).write_bytes(setup.read_bytes())
    bad_overlay = create(work / 'tab-overlay', real, HERE / '.lake/build/bin/heavy_observe')
    child = subprocess.run([str(bad_overlay / 'bin/lean'), *compiler_args], cwd=unsupported,
                           env=env, capture_output=True, timeout=5)
    assert child.returncode == 0, child.stderr
    bad_record, = (bad_overlay / 'records').glob('process-*.json')
    export('unsupported-path', {**request, 'records': [str(bad_record)]}, cwd=unsupported)
    for argv in (['--manifest'], ['--manifest', '--padding-kib', '1'], ['--bogus']):
        p = subprocess.run([str(HERE / '.lake/build/bin/compiler_advice'), *argv], cwd=work,
                           capture_output=True, text=True)
        assert p.returncode != 0 and not p.stdout and p.stderr
    def mutate(name, **fields):
        changed = {**raw, **fields}
        invoke(name, [changed], samples=0)

    # Every cohort component, never just the filename/job kind.
    for key in ('source', 'cwd', 'source_before', 'source_after', 'real_compiler',
                'compiler_fingerprint', 'compiler_version', 'compiler_githash', 'setup', 'setup_fingerprint'):
        mutate('changed-' + key, **{key: raw[key] + '-changed'})
        mutate('missing-' + key, **{key: None})
    for key in ('setup', 'setup_fingerprint'):
        changed = dict(raw); del changed[key]
        invoke('absent-' + key, [changed], samples=0, rejected=1)
    mutate('wrong-module', source='Other.lean')
    mutate('changed-args', args=[*compiler_args, '-q'])
    mutate('missing-args', args=None)
    mutate('cross-boot', boot_id='other-boot')
    mutate('old-no-boot', boot_id=None)
    no_boot = dict(raw); del no_boot['boot_id']
    invoke('old-absent-boot', [no_boot], samples=0)
    for key in ('launch_errno', 'exec_errno', 'wait_errno', 'clock_errno'):
        mutate('error-' + key, **{key: 5})
    mutate('nonzero-child', raw_wait_status=256)
    mutate('signal-child', raw_wait_status=9)
    mutate('absent-child', child_pid=0)
    mutate('reversed-clock', start_monotonic_ns=raw['end_monotonic_ns'] + 1)
    mutate('future', end_monotonic_ns=10**30)
    mutate('zero-peak', peak_rss_kib=0, measured_peak_rss_kib=0)
    mutate('inconsistent-measurement', measured_peak_rss_kib=raw['peak_rss_kib'] + 1)
    mutate('wrong-family', family='clang')
    mutate('query', input_kind='query')
    for key in ('schema', 'launch_errno', 'exec_errno', 'wait_errno', 'clock_errno', 'raw_wait_status',
                'child_pid', 'start_monotonic_ns', 'end_monotonic_ns', 'peak_rss_kib', 'measured_peak_rss_kib'):
        for suffix, value in (('negative', -1), ('fractional', 0.5), ('string', '0'), ('null', None), ('bool', False)):
            mutate(key + '-' + suffix, **{key: value})
        changed = dict(raw); del changed[key]
        invoke('absent-' + key, [changed], samples=0, rejected=1)
    # Schema 3 is a raw JSON adapter control derived from the actual schema 2
    # child, not a claim that this fixture exercised the admission controller.
    gated = {**raw, 'schema': 3, 'gate_errno': 0, 'child_present': True, 'wrapper_code': 0}
    invoke('schema3', [gated], expected=raw['peak_rss_kib'], samples=1)
    for key, value in (('gate_errno', 5), ('child_present', False), ('wrapper_code', 125),
                       ('gate_errno', 0.5), ('child_present', 'true'), ('wrapper_code', None)):
        invoke(f'schema3-{key}-{value}', [{**gated, key: value}], samples=0)
    for key in ('gate_errno', 'child_present', 'wrapper_code'):
        changed = dict(gated); del changed[key]
        invoke('schema3-missing-' + key, [changed], samples=0, rejected=1)
    invoke('malformed-json', ['{'], samples=0, rejected=1)
    invoke('empty-history', [], samples=0)
    for key, value in (('minimum_samples', 2), ('minimum_samples', 0), ('recent_count', 0),
                       ('cutoff_monotonic_ns', 10**30)):
        invoke(f'policy-{key}-{value}', req={**request, key: value})
    end = raw['end_monotonic_ns']
    invoke('equal-cutoff', req={**request, 'cutoff_monotonic_ns': end},
           expected=raw['peak_rss_kib'], samples=1)
    invoke('past-cutoff', req={**request, 'cutoff_monotonic_ns': end + 1}, samples=0)
    history = [{**raw, 'start_monotonic_ns': end-10, 'end_monotonic_ns': end-delta,
                'peak_rss_kib': peak, 'measured_peak_rss_kib': peak}
               for delta, peak in ((4, 999), (1, 10), (1, 30), (2, 20))]
    invoke('bounded-tie-maximum', history, req={**request, 'recent_count': 2}, expected=30, samples=2)
    invoke('bounded-tie-reversed', list(reversed(history)), req={**request, 'recent_count': 1}, expected=30, samples=1)
    invoke('exact-maximum', history, expected=999, samples=4)
    invoke('strict-minimum', history, req={**request, 'recent_count': 2, 'minimum_samples': 3}, samples=2)
    # Current identity comes from real files, not a request's claimed hashes.
    source.write_text('def tiny : Nat := 5\n')
    invoke('current-source-changed', samples=0)
    export('changed-source')
    source.unlink()
    invoke('current-source-missing')
    source.write_text('def tiny : Nat := 4\n')
    old_setup = setup.read_bytes(); setup.write_bytes(old_setup + b' ')
    invoke('current-setup-changed', samples=0)
    setup.unlink(); invoke('current-setup-missing')
    setup.write_bytes(old_setup)
    invoke('current-flags-changed', req={**request, 'args': [*compiler_args, '-q']}, samples=0)
    invoke('current-compiler-missing', req={**request, 'real_compiler': str(work / 'absent-lean')})
    other = work / 'other-project'; other.mkdir()
    (other / source.name).write_bytes(source.read_bytes()); (other / setup.name).write_bytes(setup.read_bytes())
    invoke('current-other-project', cwd=other, samples=0)
    for key in ('recent_count', 'minimum_samples', 'cutoff_monotonic_ns'):
        for suffix, value in (('fractional', 0.5), ('missing', None), ('string', '1')):
            invoke('request-' + key + '-' + suffix, req={**request, key: value})
    report = dict(wall_seconds=time.monotonic()-start, fixture_compilations=1,
                  raw_record=str(record_path), cases=evidence, limits='raw mutations are test controls, not additional measurements')
    (work / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(cases=len(evidence), wall_seconds=report['wall_seconds'], report=str(work / 'report.json'))))


if __name__ == '__main__':
    main()
