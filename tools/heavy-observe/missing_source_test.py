#!/usr/bin/env python3
"""Actual pinned-compiler source identity errors, without a Lake workload.
All state/permissions/symlinks are private to this bounded producer test.
Select the active repository toolchain or HEAVY_TEST_REAL_LEAN explicitly;
canonicalize once and use that same executable for hashes/calls/records.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
REAL = Path(os.environ.get('HEAVY_TEST_REAL_LEAN') or
            (subprocess.check_output(['lean', '--print-prefix'], text=True).strip() + '/bin/lean')).resolve(strict=True)


def run(command, cwd, env):
    p = subprocess.run(list(map(str, command)), cwd=cwd, env=env, capture_output=True, timeout=5)
    return dict(command=list(map(str, command)), status=p.returncode, stdout=p.stdout.decode(), stderr=p.stderr.decode())


def main():
    if sys.argv[1:2] == ['--producer']:
        directory, shim, source = map(Path, sys.argv[2:])
        if directory.name == 'malformed':
            (Path(os.environ['HEAVY_BUDGET_DIR']) / 'requests').write_text('malformed')
        result = run([shim, source], directory, os.environ)
        (directory / 'gated.json').write_text(json.dumps(result, indent=2)+'\n')
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bin', type=Path, default=HERE / '.lake/build/bin')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--expect-old', action='store_true')
    args = parser.parse_args()
    if args.output:
        work = args.output.absolute(); work.mkdir(parents=True, exist_ok=False)
    else:
        (HERE / 'test-work').mkdir(exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix='missing-source-', dir=HERE / 'test-work'))
    binary = args.bin.absolute()
    env = dict(os.environ)
    for name in ('HEAVY_BUDGET_DIR','HEAVY_OBSERVE_DIR','LEAN_SYSROOT','LAKE_OVERRIDE_LEAN'):
        env.pop(name, None)
    pure = None
    if not args.expect_old:
        result = subprocess.run([str(binary/'budget_tests')], capture_output=True, timeout=3)
        assert result.returncode == 0, result.stderr
        pure = result.stdout.decode()
    report = dict(pure=pure, expected='old caller failure' if args.expect_old else 'compiler compatibility',
        binaries={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (binary/'heavy_observe',binary/'budget_session',REAL)}, cases=[])
    for case in ('missing','not-directory','symlink-loop','malformed'):
        begin=time.monotonic(); directory=work/case; directory.mkdir()
        overlay=directory/'overlay'; (overlay/'bin').mkdir(parents=True); (overlay/'records').mkdir()
        shim=overlay/'bin/lean'; shim.write_bytes((binary/'heavy_observe').read_bytes()); shim.chmod(0o700)
        (overlay/'real-lean.path').write_text(str(REAL)+'\n')
        source=directory/'Absent.lean'
        if case=='not-directory':
            parent=directory/'plain-file'; parent.write_text('not a directory'); source=parent/'Input.lean'
        if case=='symlink-loop':
            source=directory/'Loop.lean'; source.symlink_to(source.name)
        ordinary=run([REAL,source],directory,env)
        observed=run([shim,source],directory,env)
        assert ordinary['status']==observed['status']==1, (case,ordinary,observed)
        assert (ordinary['stdout'],ordinary['stderr'])==(observed['stdout'],observed['stderr'])
        manifest=directory/'manifest'; manifest.write_text('')
        command=[binary/'budget_session',directory/'session','10','1','9','2500',manifest,'--',
                 '/usr/bin/python3','-I',Path(__file__).resolve(),'--producer',directory,shim,source]
        session=run(command,directory,env); assert session['status']==0,session
        gated=json.loads((directory/'gated.json').read_text())
        rows=[json.loads(p.read_text()) for p in (overlay/'records').glob('process-*.json')]
        gated_rows=[r for r in rows if r['schema']==3]
        row=dict(case=case,ordinary=ordinary,observe_only=observed,session=session,gated=gated,records=rows,seconds=time.monotonic()-begin)
        if args.expect_old:
            assert gated['status']==125 and 'setup failed' in gated['stderr'] and not gated_rows,row
        elif case=='malformed':
            assert gated['status']==125 and 'invalid request demand' in gated['stderr'] and not gated_rows,row
        else:
            assert (gated['status'],gated['stdout'],gated['stderr'])==(ordinary['status'],ordinary['stdout'],ordinary['stderr']),row
            assert len(gated_rows)==1,row
            r=gated_rows[0]
            assert r['gate_errno']==0 and r['child_present'] and r['result_kind']==0 and r['result_detail']==1 and r['raw_wait_status']==256
            assert r['wrapper_code']==r['shell_code']==1 and r['requested_reservation_kib']==9
            assert r['request_provenance']=='explicit-unknown-fallback' and r['reservation_ticket']>0
            assert r['parent_headroom_kib']+r['held_before_kib']+r['requested_reservation_kib']<=r['allowance_kib']
            assert r['source_before'] is None and r['source_after'] is None and not r['identity_complete']
            assert r['source']==str(source) and r['input_kind']=='file' and r['real_compiler']==str(REAL)
            assert r['compiler_version'] and r['compiler_githash'] and r['input_closure'] is None
        report['cases'].append(row)
        (work/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(report=str(work/'report.json'),expected=report['expected'],cases=[c['case'] for c in report['cases']])))


if __name__=='__main__': main()
