#!/usr/bin/env python3
"""Finite caller coverage for active/explicit pinned-compiler discovery.
Copy only the installed executable into an owned temporary view, delegating
installed immutable assets read-only in use; no package/cache installation.
"""
import atexit
import shutil
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def query(exe, flag, env):
    return subprocess.check_output([str(exe), flag], env=env, text=True, timeout=5).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--harness', type=Path, default=HERE / 'missing_source_test.py')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--expect-old', action='store_true')
    args = parser.parse_args()
    env = dict(os.environ)
    source = Path(env.get('HEAVY_TEST_REAL_LEAN') or
                  (subprocess.check_output(['lean', '--print-prefix'], text=True, timeout=5).strip() + '/bin/lean')).resolve(strict=True)
    prefix = Path(query(source, '--print-prefix', env)).resolve(strict=True)
    if args.output:
        work = args.output.absolute(); work.mkdir(parents=True, exist_ok=False)
    else:
        (HERE / 'test-work').mkdir(exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix='compiler-discovery-', dir=HERE / 'test-work'))
        atexit.register(shutil.rmtree, work, ignore_errors=True)
    view = work / 'portable'; (view / 'bin').mkdir(parents=True)
    selected = view / 'bin/lean'; selected.write_bytes(source.read_bytes()); selected.chmod(0o700)
    for name in ('lib', 'include', 'share', 'src'):
        if (prefix / name).exists(): (view / name).symlink_to(prefix / name, target_is_directory=True)
    clean = dict(env)
    for name in ('HEAVY_TEST_REAL_LEAN', 'HEAVY_BUDGET_DIR', 'HEAVY_OBSERVE_DIR', 'LEAN_SYSROOT', 'LAKE_OVERRIDE_LEAN'):
        clean.pop(name, None)
    assert selected.resolve(strict=True) != source and digest(selected) == digest(source)
    assert Path(query(selected, '--print-prefix', clean)).resolve(strict=True) == view
    identity = {flag: query(source, flag, clean) for flag in ('--version', '--githash')}
    assert identity == {flag: query(selected, flag, clean) for flag in identity}
    report = dict(source=str(source), selected=str(selected), sha256=digest(selected), identity=identity,
                  expected='old selection defect' if args.expect_old else 'portable selection', routes=[])
    for route in ('active', 'explicit'):
        variables = dict(clean)
        # An actual compiler in PATH, not a script returning a supplied prefix.
        variables['PATH'] = str(view / 'bin') + os.pathsep + variables['PATH']
        if route == 'explicit':
            variables['PATH'] = clean['PATH']
            variables['HEAVY_TEST_REAL_LEAN'] = str(selected)
        command = ['/usr/bin/python3', '-I', str(args.harness.resolve()), '--bin', str(HERE / '.lake/build/bin'),
                   '--output', str(work / route)]
        p = subprocess.run(command, env=variables, capture_output=True, timeout=10)
        (work / (route + '.stdout')).write_bytes(p.stdout); (work / (route + '.stderr')).write_bytes(p.stderr)
        assert p.returncode == 0, (route, p.returncode, p.stdout, p.stderr)
        controls = json.loads((work / route / 'report.json').read_text())
        assert len(controls['cases']) == 4
        selected_hash = controls['binaries'].get(str(selected))
        commands_match = all(c['ordinary']['command'][0] == str(selected) for c in controls['cases'])
        records = [r for c in controls['cases'] for r in c['records']]
        records_match = bool(records) and all(r['real_compiler'] == str(selected) for r in records)
        matched = selected_hash == digest(selected) and commands_match and records_match
        report['routes'].append(dict(route=route, command=command, status=p.returncode,
            selected_hash=selected_hash, direct_commands_match=commands_match, records_match=records_match,
            matched=matched, actual_report=str(work / route / 'report.json')))
        (work / 'report.json').write_text(json.dumps(report, indent=2)+'\n')
        assert matched != args.expect_old, report['routes'][-1]
    print(json.dumps(dict(report=str(work / 'report.json'), expected=report['expected'])))


if __name__ == '__main__': main()
