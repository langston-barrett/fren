#!/usr/bin/env python3
"""Owned production-object SIGPIPE controls and injected note-write faults."""
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
BIN = HERE / '.lake/build/bin'
prefix = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())
rsp = shlex.split((BIN / 'heavy_observe.rsp').read_text())
with tempfile.TemporaryDirectory(prefix='heavy-notice-') as tmp:
    work = Path(tmp)
    def run(cmd, **kwargs):
        p = subprocess.run(list(map(str, cmd)), capture_output=True, timeout=40, **kwargs)
        assert p.returncode == 0, (cmd, p.returncode, p.stdout, p.stderr)
        return p
    common = ['cc', '-I', prefix / 'include', '-std=gnu17', '-Wall', '-Wextra', '-Werror', '-c']
    probeobj = work / 'probe.o'
    run([*common, HERE / 'notice_signal_probe.c', '-o', probeobj])
    probe = work / 'probe'
    link = [prefix / 'bin/clang', probeobj, HERE / '.lake/build/observer.o',
            '-Wl,--wrap=write', '-Wl,--wrap=sigtimedwait', '-o', probe, *rsp[rsp.index('-L'):]]
    run(link)
    records = {}
    for case in ['unrelated-on-success', 'closed-pipe', 'preexisting', 'interrupted-drain', 'absent-stderr', 'full-device']:
        p = run([probe, case]); first, second = map(json.loads, p.stdout.decode().splitlines())
        assert first['mask_preserved'] and first['default_disposition_preserved'] and first['io_ok'], first
        assert first['after_pending'] == (1 if case in ('unrelated-on-success', 'preexisting') else 0), first
        assert first['before_pending'] == (1 if case == 'preexisting' else 0), first
        if case == 'unrelated-on-success': assert second['write_result'] > 0 and second['injected_external']
        if case == 'interrupted-drain': assert second['write_errno'] == 32 and second['injected_eintr']
        if case == 'closed-pipe': assert second['write_errno'] == 32
        if case == 'absent-stderr': assert second['write_errno'] == 9
        if case == 'full-device': assert second['write_errno'] == 28
        records[case] = [first, second]
    faultobj = work / 'fault.o'; run([*common, HERE / 'notice_fault.c', '-o', faultobj])
    observer = work / 'fault-observer'
    run([prefix / 'bin/clang', faultobj, *rsp[:rsp.index('-L')], '-Wl,--wrap=write',
         '-Wl,--wrap=sigtimedwait', '-o', observer, *rsp[rsp.index('-L'):]])
    for fault in ('EBADF', 'ENOSPC', 'EINTR'):
        marker = work / ('injected-' + fault)
        env = dict(os.environ, HEAVY_TEST_OBSERVER=str(observer), HEAVY_NOTICE_FAULT=fault,
                   HEAVY_NOTICE_FAULT_MARKER=str(marker))
        p = run([sys.executable, '-I', HERE / 'feedback_test.py'], env=env)
        assert marker.read_bytes(), fault
        records['injected-' + fault] = json.loads(p.stdout)
        records['injected-' + fault]['injection_count'] = marker.stat().st_size
    print(json.dumps(records, indent=2))
