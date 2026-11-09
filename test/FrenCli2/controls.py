#!/usr/bin/env python3
"""Run the actual source command, including owned physical failure controls.

No constructor-only driver, expected-output fixture, network or shell is used.
The temporary tree isolates its fixed solver path from the shipped real cvc5.
"""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time


def sha(path):
    with Path(path).open('rb') as handle:
        return hashlib.file_digest(handle, 'sha256').hexdigest()


def main():
    exe = Path(sys.argv[1]).resolve()
    root = exe.parents[3]
    evidence = os.environ.get('FREN2_COMMAND_EVIDENCE_DIR')
    rows = []
    with tempfile.TemporaryDirectory(prefix='fren2-source-command-') as temporary:
        tmp = Path(temporary)
        source = tmp / 'source space;$(false)`false`\nfile.fren'
        sentinel = tmp / 'unexpected-shell-write'

        def run(label, text=None, options=(), expected=0, verdict='verified', binary=exe, path=source):
            if text is not None:
                path.write_bytes(text.encode() if isinstance(text, str) else text)
            command = [str(binary), *options, str(path)]
            started = time.monotonic()
            p = subprocess.run(command, cwd=tmp, capture_output=True, timeout=12)
            output = json.loads(p.stdout)
            row = dict(label=label, command=command, exit_code=p.returncode,
                       seconds=time.monotonic()-started, output=output,
                       stdout_hex=p.stdout.hex(), stderr_hex=p.stderr.hex(),
                       binary_sha256=sha(binary), source_hex=path.read_bytes().hex() if path.exists() else None)
            rows.append(row)
            assert p.returncode == expected, row
            assert output['exit_code'] == expected and output['verdict'] == verdict, row
            assert output['file'] == str(path), row
            assert p.stderr == b'', row
            assert not sentinel.exists(), 'path passed to a shell'
            return output

        good = 'mod command\nfn next(n: Int): Int := n + 1\nexpect safe(n: Int) { assume a: n >= 0 expect grows: next(n) > n }'
        verified = run('verified', good)
        assert verified['checks'] and all(r['status'] in ['verified', 'witness'] for r in verified['checks'])
        assert any(r['status'] == 'witness' and r['assignment_summary'] is not None for r in verified['checks'])
        assert all(r['owner'] and r['reason'] for r in verified['checks'])
        bad = 'mod command\nexpect bad(n: Int) { assume a: n = 2 expect wrong: n = 3 }'
        refuted = run('refuted', bad, expected=1, verdict='refuted')
        counter = next(r for r in refuted['checks'] if r['status'] == 'counterexample')
        assert counter['owner'].endswith('.bad') and counter['location'] and counter['model_ref']
        assert counter['assignment_summary']['values'] == [{'parameter_index': 0, 'value': '2'}]
        assert counter['location']['start_byte'] == bad.encode().index(b'n = 3')
        inconsistent = run('inconsistent', 'mod command\nexpect c(n: Int) { assume a: n = 0 assume b: n = 1 expect bad: false }', expected=2, verdict='inconsistent')
        assert any(r['status'] == 'vacuous' for r in inconsistent['checks'])
        for label, text in [('no-module-checks', 'mod empty'), ('no-block-checks', 'mod empty\nexpect empty() {}')]:
            run(label, text, expected=4, verdict='noChecks')
        for label, text, token in [
                ('parse', 'mod command\r\nexpect c() { expect bad: }', b'}'),
                ('resolution-bytes', '-- λ\r\nmod command\r\nexpect c() { expect bad: absent }', b'absent'),
                ('type', 'mod command\nexpect c() { expect bad: 1 + true = 2 }', None)]:
            result = run(label, text, expected=5, verdict='inputFailure')
            span = result['diagnostic']['location']
            assert 0 <= span['start_byte'] <= span['stop_byte'] <= len(text.encode()), result
            if token:
                assert span['start_byte'] == text.encode().index(token), result
        run('invalid-utf8', b'mod command\n\xff', expected=5, verdict='inputFailure')
        run('oversize-source', b' ' * 1048577, expected=5, verdict='inputFailure')
        run('missing-file', path=tmp/'missing.fren', expected=5, verdict='inputFailure')
        dash = tmp/'-source.fren'
        # A relative dash path exercises the parser's end-of-options marker.
        dash.write_text(good)
        dash_result = subprocess.run([str(exe), '--', dash.name], cwd=tmp, capture_output=True, timeout=12)
        assert dash_result.returncode == 0 and json.loads(dash_result.stdout)['verdict'] == 'verified'
        rows.append(dict(label='dash-path', command=[str(exe), '--', dash.name], exit_code=dash_result.returncode,
                         output=json.loads(dash_result.stdout), binary_sha256=sha(exe)))
        # This path would create a marker if ever interpolated into a shell.
        run('shell-path', good, path=tmp/('$(touch unexpected-shell-write).fren'))
        for label, opts, status in [
                ('real-unknown', ['--solver-resources', '1'], 'unknown'),
                ('script-limit', ['--input-bytes', '1'], 'resourceExhausted'),
                ('evaluation-limit', ['--evaluation-depth', '0'], 'unconfirmed')]:
            result = run(label, good, options=opts, expected=3, verdict='inconclusive')
            assert any(r['status'] == status for r in result['checks']), result
        definedness = run('definedness-confirmation', 'mod command\nexpect c() { expect goal: 1 div 0 = 0 }', expected=1, verdict='refuted')
        assert any(r['status'] == 'counterexample' and r['model_ref'] and r['assignment_summary']['confirmation'] == 'FrenOirToSmt.Confirmation.counterexample' for r in definedness['checks'])

        for args in [[], ['--bogus', '1', str(source)], ['--wall-ms', '0', str(source)],
                     ['--wall-ms', '10001', str(source)], ['--solver-ms', '0', str(source)],
                     ['--solver-resources', '1000000001', str(source)], ['--output-bytes', '1048577', str(source)],
                     ['--input-bytes', '0', str(source)], ['--evaluation-depth', '10001', str(source)],
                     ['--wall-ms', '-1', str(source)], ['--wall-ms', '1x', str(source)],
                     ['--wall-ms'], ['-source.fren'], [str(source), str(source)]]:
            p = subprocess.run([str(exe), *args], cwd=tmp, capture_output=True, timeout=12)
            result = json.loads(p.stdout)
            assert p.returncode == 5 and result['verdict'] == 'inputFailure', (args, p, result)
            rows.append(dict(label='argument-failure', command=[str(exe), *args], exit_code=p.returncode, output=result))
        p = subprocess.run([str(exe), '--help'], capture_output=True, timeout=12)
        assert p.returncode == 0 and b'Usage: fren2_check' in p.stdout
        rows.append(dict(label='help', command=[str(exe), '--help'], exit_code=p.returncode, stdout=p.stdout.decode()))

        isolated = tmp/'owned tree'
        binary = isolated/'.lake/build/bin/fren2_check'
        binary.parent.mkdir(parents=True)
        shutil.copyfile(exe, binary)
        binary.chmod(0o755)
        helper = isolated/'src/FrenOirToSmt/transport.py'
        helper.parent.mkdir(parents=True)
        shutil.copyfile(root/'src/FrenOirToSmt/transport.py', helper)
        solver = isolated/'.lake/packages/cvc5/cvc5-Linux-x86_64-static/bin/cvc5'
        solver.parent.mkdir(parents=True)
        shutil.copyfile(root/'test/FrenCli2/solver_fixture.py', solver)
        solver.chmod(0o755)
        for mode, status in [('unknown', 'unknown'), ('unsupported', 'unsupported'),
                             ('nonzero', 'processFailure'), ('stderr', 'processFailure'),
                             ('protocol', 'processFailure'), ('bytes', 'processFailure'),
                             ('flood', 'resourceExhausted'), ('timeout', 'resourceExhausted')]:
            solver.with_suffix('.mode').write_text(mode)
            result = run('owned-'+mode, good, options=['--wall-ms', '100', '--output-bytes', '64'],
                         expected=3, verdict='inconclusive', binary=binary)
            assert any(r['status'] == status for r in result['checks']), (mode, result)
        solver.unlink()
        missing = run('missing-solver', good, expected=3, verdict='inconclusive', binary=binary)
        assert any(r['status'] == 'processFailure' for r in missing['checks'])
        helper.unlink()
        missing = run('missing-helper', good, expected=3, verdict='inconclusive', binary=binary)
        assert any(r['status'] == 'processFailure' for r in missing['checks'])
        for row in rows:
            if 'output' in row:
                assert '(check-sat)' not in json.dumps(row['output']), 'raw script dumped'
        if evidence:
            target = Path(evidence)
            target.mkdir(parents=True, exist_ok=True)
            (target/f'command-{os.getpid()}.json').write_text(json.dumps(dict(
                executable=str(exe), executable_sha256=sha(exe), cases=rows), indent=2)+'\n')
    print(f'source-command-controls: {len(rows)} actual command invocations; real cvc5 outcomes and owned physical failures')


if __name__ == '__main__':
    main()
