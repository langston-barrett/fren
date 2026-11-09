#!/usr/bin/env python3
"""Small ordinary-build and raw-evidence controls; each partition targets 30s."""
import fcntl
import hashlib
import importlib.util
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
from publish import publish
from history import snapshot
from owned_test import run as owned_run


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'positive'
    assert mode in ('positive', 'evidence', 'store')
    parent = Path(os.environ.get('HEAVY_AUTOMATIC_TEST_ROOT', HERE / 'test-work'))
    parent_existed = parent.exists()
    if os.environ.get('HEAVY_AUTOMATIC_REQUIRE_FRESH') == '1':
        assert not parent_existed, parent
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix='automatic-', dir=parent))
    (work / 'setup.json').write_text(json.dumps(dict(mode=mode, parent=str(parent),
        parent_preexisting=parent_existed, created_parent=True)))
    configured = os.environ.get('HEAVY_TEST_REAL_LEAN')
    if configured is None:
        prefix = owned_run(['lean', '--print-prefix'], directory=work, label='prefix',
                           timeout=3, check=True).stdout.decode().strip()
        configured = prefix + '/bin/lean'
    real = Path(configured).resolve()
    pkg = work / 'pkg'; pkg.mkdir()
    (pkg / 'lean-toolchain').write_text((ROOT / 'lean-toolchain').read_text())
    (pkg / 'lakefile.toml').write_text('name = "auto_control"\nenableArtifactCache = false\n[[lean_lib]]\nname = "Tiny"\n')
    source = pkg / 'Tiny.lean'; source.write_text('''def tiny : Nat := 42
#eval tiny
#eval show IO Unit from do
  if (← IO.getEnv "AUTO_TEST_FAIL") == some "yes" then
    throw (IO.userError "intentional compiler failure")
#eval show IO Unit from do
  if let some dir ← IO.getEnv "HEAVY_BUDGET_DIR" then
    for entry in (← System.FilePath.readDir dir) do
      if entry.fileName.startsWith "ticket-" then
        IO.println ("HEAVY_RUNNING " ++ (← IO.FS.readFile entry.path).trimAscii.copy)
''')
    # Private fixture home only, with explicit installed toolchain/cache paths;
    # no coordinator HOME, global store or package cache is changed.
    home = work / 'home'; home.mkdir()
    env = dict(os.environ, HOME=str(home), TMPDIR=str(work),
               ELAN_HOME=os.environ.get('ELAN_HOME', '/opt/elan'), LAKE_CACHE_DIR=str(work / 'cache'),
               HEAVY_MEM_GB='1.5', HEAVY_SLOTS='1', HEAVY_MAX_LOAD='off',
               FREN_BUILD_ALLOWANCE_KIB='1300000', FREN_BUILD_HEADROOM_KIB='100000',
               FREN_BUILD_FALLBACK_KIB='600000', FREN_BUILD_PADDING_KIB='123456',
               FREN_BUILD_TIMEOUT_MS='5000', HEAVY_COMPILER_CPU_SECONDS='10', HEAVY_COMPILER_WALL_MS='5000')
    for key in ('HEAVY_BUDGET_DIR', 'LEAN_SYSROOT', 'LAKE_OVERRIDE_LEAN', 'HEAVY_OBSERVE_DIR',
                'HEAVY_LOG', 'FREN_BUILD_REQUESTS_FILE'):
        env.pop(key, None)
    receipts = []
    def build(label, extra=None, expect=0, compiler_error=False):
        # Only this fixture's single compiler output; keep all warm dependencies.
        (pkg / '.lake/build/lib/lean/Tiny.olean').unlink(missing_ok=True)
        before = set(work.glob('fren-build-*'))
        start = time.monotonic()
        p = owned_run([str(ROOT / 'scripts/heavy'), '--offline', str(real.parent / 'lake'),
                            'build', '+Tiny', '--offline', '--no-cache', '--wfail'],
                           cwd=pkg, env=dict(env, **(extra or {})), directory=work, label=label, timeout=12)
        states = set(work.glob('fren-build-*')) - before
        rows = [json.loads(path.read_bytes()) for state in states
                for path in (state / 'state/overlay/records').glob('process-*.json')]
        files = [r for r in rows if r['input_kind'] == 'file']
        item = dict(case=label, status=p.returncode, stdout=p.stdout.decode(), stderr=p.stderr.decode(),
                    wall_seconds=time.monotonic()-start, states=list(map(str, states)), records=rows)
        receipts.append(item)
        (work / 'result.json').write_text(json.dumps(receipts, indent=2))
        assert p.returncode == expect, item
        if expect == 0 or compiler_error:
            assert len(files) == 1, item
            row = files[0]
            assert row['gate_errno'] == 0 and row['child_present'] and row['raw_wait_status'] == (256 if compiler_error else 0)
            assert row['compiler_cpu_limit_seconds'] == 10 and row['compiler_wall_applied_ms'] == 5000
            assert row['reservation_ticket'] > 0 and row['admission_granted_ns'] > 0
            # The actual admission snapshot charged this sole held compiler row.
            running = [line.split('HEAVY_RUNNING ', 1)[1].split() for line in item['stdout'].splitlines()
                       if 'HEAVY_RUNNING ' in line]
            assert len(running) == 1 and int(running[0][0]) == row['reservation_ticket']
            assert running[0][1] == '1' and int(running[0][2]) == row['requested_reservation_kib']
            item['actual_running_lease'] = running[0]
            assert row['held_before_kib'] + row['requested_reservation_kib'] + row['parent_headroom_kib'] <= row['allowance_kib']
            if compiler_error:
                assert row['artifacts'][0]['fingerprint'] is None
                return row
            assert row['artifacts'][0]['fingerprint']
            item['artifact_sha256'] = hashlib.sha256((pkg / '.lake/build/lib/lean/Tiny.olean').read_bytes()).hexdigest()
            return row
        assert not files, item
        return None

    a = build('no-history')
    assert a['request_provenance'] == 'explicit-unknown-fallback' and a['requested_reservation_kib'] == 600000
    spool = home / '.cache/heavy/compiler-observations'
    original = {p.name: p.read_bytes() for p in spool.glob('*.json')}
    assert len(original) == 1, original
    def restore(data=original):
        for p in spool.iterdir():
            if p.name != '.lock':
                if p.is_dir(): p.rmdir()
                else: p.unlink()
        for name, raw in data.items():
            p = spool / name; p.write_bytes(raw); p.chmod(0o600)
    def raw_rows(records):
        data = {}
        for record in records:
            raw = json.dumps(record, separators=(',', ':')).encode()
            data[hashlib.sha256(raw).hexdigest() + '.json'] = raw
        restore(data)
    if mode == 'positive':
        b = build('one-sample')
        assert b['request_provenance'] == 'explicit-unknown-fallback' and b['automatic_sample_count'] == 1
        c = build('two-samples')
        assert c['request_provenance'] == 'automatic-cohort-estimate' and c['automatic_sample_count'] == 2
        assert c['requested_reservation_kib'] == max(a['peak_rss_kib'], b['peak_rss_kib']) + 123456 != 600000
        assert len({r['artifact_sha256'] for r in receipts}) == 1
        # Same compiler stream and output; Lake timing/progress is wrapper output.
        assert all('42' in r['stdout'] for r in receipts)
        def streams(item):
            output = re.sub(r'HEAVY_RUNNING [^\n]+', 'HEAVY_RUNNING RECEIPT', item['stdout'])
            output = re.sub(r'(Built Tiny )\([0-9.]+(?:ms|s)\)', r'\1(TIME)', output)
            setup = {'info: auto_control: no previous manifest, creating one from scratch',
                     'info: toolchain not updated; already up-to-date'}
            error = '\n'.join(line for line in item['stderr'].splitlines()
                              if not line.startswith('fren-build: retained private state: ') and line not in setup)
            return output, error
        # Compare the real ordinary-build streams across fallback and automatic
        # admission, excluding only the fixture receipt and Lake's setup/timing.
        assert len({streams(item) for item in receipts}) == 1

        explicit = work / 'explicit.tsv'
        explicit.write_text(f"{source}\t{a['source_before']}\t444444\n")
        d = build('explicit-wins', {'FREN_BUILD_REQUESTS_FILE': str(explicit)})
        assert d['request_provenance'] == 'explicit-source-request' and d['requested_reservation_kib'] == 444444
        for padding in ('0', 'bad', str(2**50)):
            unknown = build('invalid-advice-padding-' + padding, {'FREN_BUILD_PADDING_KIB': padding})
            assert unknown['request_provenance'] == 'explicit-unknown-fallback' and unknown['requested_reservation_kib'] == 600000
        explicit_padding = build('explicit-wins-invalid-advice-padding',
                                 {'FREN_BUILD_REQUESTS_FILE': str(explicit), 'FREN_BUILD_PADDING_KIB': 'bad'})
        assert explicit_padding['request_provenance'] == 'explicit-source-request' and explicit_padding['requested_reservation_kib'] == 444444
        failed = build('automatic-compiler-error', {'AUTO_TEST_FAIL': 'yes'}, expect=1, compiler_error=True)
        assert failed['request_provenance'] == 'automatic-cohort-estimate' and failed['automatic_sample_count'] == 2
        native = owned_run([str(real), *failed['args']], cwd=pkg,
                           env=dict(env, AUTO_TEST_FAIL='yes'), directory=work,
                           label='native-error-comparison', timeout=5)
        assert native.returncode == failed['shell_code'] == 1
        assert b'intentional compiler failure' in native.stdout and 'intentional compiler failure' in receipts[-1]['stdout']
        receipts[-1]['native_comparison'] = dict(status=native.returncode, stdout=native.stdout.decode(), stderr=native.stderr.decode())
        explicit.write_text('malformed\n')
        build('invalid-manifest-no-launch', {'FREN_BUILD_REQUESTS_FILE': str(explicit)}, expect=125)
    elif mode == 'evidence':
        # Literal raw records, passed through the real snapshot reader and
        # native decoder/selection. No supplied successful eligibility flag.
        second = dict(a, child_pid=a['child_pid']+1, end_monotonic_ns=a['end_monotonic_ns']+1)
        cases = [('boot_id', 'other-boot'), ('source_before', 'changed-source'),
                 ('compiler_fingerprint', 'changed-compiler'), ('args', ['Tiny.lean']),
                 ('setup_fingerprint', 'changed-setup'), ('cwd', '/other'),
                 ('raw_wait_status', 256), ('gate_errno', 5), ('child_present', False),
                 ('wrapper_code', 124), ('end_monotonic_ns', 0)]
        # Partition by running decoder controls in-process below; only a few
        # full builds are needed to establish actual fallback/charged wiring.
        for key, value in cases:
            records = [dict(a, **{key: value}), dict(second, **{key: value})]
            raw_rows(records)
            if key in ('boot_id', 'source_before', 'raw_wait_status'):
                row = build('mismatch-' + key)
                assert row['request_provenance'] == 'explicit-unknown-fallback' and row['requested_reservation_kib'] == 600000
            else:
                # The actual adviser uses the shared raw decoder/sample selector.
                request = work / 'advice.json'
                request.write_text(json.dumps(dict(real_compiler=str(real), args=a['args'], records=[str(p) for p in spool.glob('*.json')],
                                                   cutoff_monotonic_ns=0, recent_count=2, minimum_samples=2)))
                p = owned_run([str(HERE / '.lake/build/bin/compiler_advice'), str(request)], cwd=pkg,
                              env=env, directory=work, label='advice-' + key, timeout=3)
                assert p.returncode == 0 and json.loads(p.stdout)['status'] == 'unknown', (key, p)
        raw_rows([dict(a, peak_rss_kib=2000000, measured_peak_rss_kib=2000000),
                  dict(second, peak_rss_kib=2000000, measured_peak_rss_kib=2000000)])
        row = build('estimate-does-not-fit-session')
        assert row['automatic_sample_count'] == 2 and row['request_provenance'] == 'explicit-unknown-fallback'
        assert row['requested_reservation_kib'] == 600000
        # Literal Unicode separators inside an unrelated raw string are valid
        # JSON bytes, not extra physical records. Exercise the native consumer.
        literal = dict(a, unrelated="literal\u0085\u2028\u2029separators")
        raw = json.dumps(literal, ensure_ascii=False, separators=(',', ':')).encode()
        other_raw = json.dumps(dict(second, unrelated=literal['unrelated']), ensure_ascii=False, separators=(',', ':')).encode()
        assert b'\xe2\x80\xa8' in raw
        restore({hashlib.sha256(data).hexdigest() + '.json': data for data in (raw, other_raw)})
        row = build('literal-separators')
        assert row['request_provenance'] == 'automatic-cohort-estimate' and row['automatic_sample_count'] == 2
        # Replace source bytes at the actual history-read boundary, after the
        # gate captured context. Revalidation must discard otherwise known advice.
        raw_rows([a, second])
        hook = work / 'mutate.c'
        hook.write_text(r'''#define _GNU_SOURCE
#include <fcntl.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <unistd.h>
int open(const char *p, int flags, ...) {
    mode_t mode = 0;
    if (flags & O_CREAT) { va_list a; va_start(a, flags); mode = va_arg(a, int); va_end(a); }
    if ((flags & O_PATH) && strstr(p, "/compiler-history.json")) {
        const char *source = getenv("AUTO_MUTATE_SOURCE");
        const char *marker = getenv("AUTO_MUTATE_MARKER");
        if (source && marker) {
            int once = syscall(SYS_openat, AT_FDCWD, marker, O_WRONLY|O_CREAT|O_EXCL, 0600);
            if (once >= 0) {
                close(once);
                int fd = syscall(SYS_openat, AT_FDCWD, source, O_WRONLY|O_APPEND, 0);
                if (fd >= 0) { const char s[] = "\n-- mutation at history read\n"; write(fd, s, sizeof(s)-1); close(fd); }
            }
        }
    }
    return syscall(SYS_openat, AT_FDCWD, p, flags, mode);
}
''')
        lib = work / 'mutate.so'
        owned_run(['cc', '-shared', '-fPIC', str(hook), '-o', str(lib)], directory=work,
                  label='mutation-helper', check=True, timeout=5)
        marker = work / 'mutated'
        row = build('source-mutated-after-capture', {'LD_PRELOAD': str(lib),
                    'AUTO_MUTATE_SOURCE': str(source), 'AUTO_MUTATE_MARKER': str(marker)})
        assert marker.exists() and row['source_before'] != row['source_after']
        assert row['automatic_sample_count'] == 2 and row['request_provenance'] == 'explicit-unknown-fallback'
        # Hash-valid but malformed/incomplete row rejects the entire snapshot.
        raw_rows([a, {'schema': 3}])
        row = build('incomplete-record')
        assert row['request_provenance'] == 'explicit-unknown-fallback'
    else:
        controls = []
        for case in ('corrupt', 'oversize', 'symlink', 'extra-entry', 'too-many', 'busy'):
            restore()
            target = spool / next(iter(original))
            held = None
            if case == 'corrupt': target.write_bytes(b'not json')
            elif case == 'oversize': target.write_bytes(b'x' * 65537)
            elif case == 'symlink': target.unlink(); target.symlink_to(source)
            elif case == 'extra-entry': (spool / 'unexpected').write_text('x')
            elif case == 'too-many':
                for n in range(257):
                    p = spool / (f'{n:064x}.json'); p.write_bytes(b'{}'); p.chmod(0o600)
            elif case == 'busy':
                held = open(spool / '.lock', 'rb'); fcntl.flock(held, fcntl.LOCK_EX | fcntl.LOCK_NB)
            try:
                assert snapshot(str(home)) is None, case
                if case in ('corrupt', 'oversize', 'busy'):
                    row = build(case)
                    assert row['request_provenance'] == 'explicit-unknown-fallback' and row['requested_reservation_kib'] == 600000
                controls.append(case)
            finally:
                if held: held.close()
        # Two valid JSON objects in one physical file are invalid input, even
        # though each object alone could be eligible. Preserve the literal LF.
        restore()
        compound = next(iter(original.values())) + b'\n' + next(iter(original.values()))
        restore({hashlib.sha256(compound).hexdigest() + '.json': compound})
        assert snapshot(str(home)) is None
        controls.append('compound-physical-record')
        receipts.append(dict(store_controls=controls))
    (work / 'result.json').write_text(json.dumps(receipts, indent=2))
    print(f'automatic {mode} controls passed: {work}')


if __name__ == '__main__': main()
