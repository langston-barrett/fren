#!/usr/bin/env python3
"""Actual private-session wall deadline controls, with retained observations."""
import json
import fcntl
import os
import shutil
import re
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
ENTRY = ROOT / 'scripts/heavy-lean-build'
work = Path(tempfile.mkdtemp(prefix='heavy-wall-'))
fixture = work / 'fixture/bin/lean'
fixture.parent.mkdir(parents=True)
source = work / 'fixture.c'
source.write_text(r'''#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdlib.h>
int main(int n, char **v) {
    if (n > 1 && !strcmp(v[1], "--print-prefix")) { char p[4096]; ssize_t k=readlink("/proc/self/exe", p, sizeof(p)-1); if(k<9)return 1; p[k-9]=0; puts(p); return 0; }
    if (n > 1 && (!strcmp(v[1], "--version") || !strcmp(v[1], "--githash"))) return 0;
    if (n > 1 && !strcmp(v[1], "busy.lean")) { volatile unsigned long x=0; for (;;) x++; }
    if (n > 1 && !strcmp(v[1], "hold.lean")) { usleep(700000); return 0; }
    if (n > 1 && !strcmp(v[1], "sleep.lean")) {
        pid_t p=fork(); if(p<0)return 3;
        if(!p) { FILE *f=fopen(getenv("WALL_DESCENDANT"), "w"); if(f){fprintf(f,"%ld\n",(long)getpid()); fclose(f);} sleep(20); return 0; }
        sleep(20); return 0;
    }
    puts("fixture ok"); return 0;
}
''')
subprocess.run(['cc', '-O2', str(source), '-o', str(fixture)], check=True)
request = work / 'requests'; request.write_text('')
results = []
fault_source = work / 'fault.c'
fault_source.write_text(r'''#define _GNU_SOURCE
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <unistd.h>
#include <fcntl.h>
ssize_t recv(int fd, void *buf, size_t len, int flags) {
    ssize_t r = syscall(SYS_recvfrom, fd, buf, len, flags, 0, 0);
    if (r > 0 && (getenv("WALL_SLOW_RECORD") || getenv("WALL_FAIL_RECORD"))) usleep(300000);
    return r;
}
ssize_t sendto(int fd, const void *buf, size_t len, int flags, const struct sockaddr *addr, socklen_t size) {
    if (getenv("WALL_FAIL_SEND")) { errno = EIO; return -1; }
    return syscall(SYS_sendto, fd, buf, len, flags, addr, size);
}
int link(const char *old, const char *new) {
    if (strstr(new, "/process-") && getenv("WALL_SLOW_RECORD")) {
        int fd = open(getenv("WALL_MARKER"), O_WRONLY | O_CREAT, 0600);
        if (fd >= 0) close(fd);
        sleep(10);
    }
    if (strstr(new, "/process-") && getenv("WALL_FAIL_RECORD")) {
        int fd = open(getenv("WALL_MARKER"), O_WRONLY | O_CREAT, 0600);
        if (fd >= 0) close(fd);
        errno = EIO; return -1;
    }
    return syscall(SYS_link, old, new);
}
''')
fault = work / 'fault.so'
subprocess.run(['cc', '-shared', '-fPIC', str(fault_source), '-o', str(fault)], check=True)
def run(label, setting, arg, fault_mode=None):
    state = work / label
    env = os.environ.copy(); env.pop('HEAVY_COMPILER_CPU_SECONDS', None)
    if setting is None: env.pop('HEAVY_COMPILER_WALL_MS', None)
    else: env['HEAVY_COMPILER_WALL_MS'] = setting
    env['WALL_DESCENDANT'] = str(work / (label + '.pid'))
    if fault_mode:
        env['LD_PRELOAD'] = str(fault)
        env[fault_mode] = '1'
        env['WALL_MARKER'] = str(work / (label + '.blocked'))
    cmd = [str(ENTRY), '--state', str(state), '--real-lean', str(fixture), '--allowance-kib', '1300000',
           '--headroom-kib', '100000', '--fallback-kib', '600000', '--timeout-ms', '30000', '--requests', str(request),
           '--', sys.executable, '-c', 'import os,subprocess,sys; p=subprocess.run([os.environ["LEAN_SYSROOT"]+"/bin/lean",sys.argv[1]]); sys.exit(128-p.returncode if p.returncode<0 else p.returncode)', arg]
    start = time.monotonic(); p = subprocess.run(cmd, env=env, cwd=work, capture_output=True, timeout=8)
    elapsed = time.monotonic() - start
    records = [json.loads(f.read_text()) for f in (state / 'overlay/records').glob('process-*.json')]
    results.append(dict(case=label, argv=cmd, wall_setting=setting, cwd=str(work), status=p.returncode, stdout=p.stdout.decode(), stderr=p.stderr.decode(), wrapper_seconds=elapsed, records=records))
    return p, records
p, rows = run('fast', '2000', 'ok.lean')
assert p.returncode == 0 and rows[0]['raw_wait_status'] == 0 and not rows[0]['wall_timeout'], results[-1]
p, rows = run('query', '200', '--version')
assert p.returncode == 0 and rows[0]['compiler_wall_applied_ms'] is None, results[-1]
p, rows = run('default', None, 'ok.lean')
assert p.returncode == 0 and rows[0]['compiler_wall_applied_ms'] is None, results[-1]
env = os.environ.copy(); env.pop('HEAVY_BUDGET_DIR', None); env['HEAVY_COMPILER_WALL_MS'] = '200'
p = subprocess.run([str(work / 'fast/overlay/bin/lean'), 'ok.lean'], env=env, cwd=work, capture_output=True, timeout=5)
results.append(dict(case='missing-session', status=p.returncode, stdout=p.stdout.decode(), stderr=p.stderr.decode()))
assert p.returncode == 125, results[-1]
for bad in ('0', '-1', 'abc', '2147483648', ''):
    p, rows = run('invalid-' + (bad or 'empty'), bad, 'ok.lean')
    assert p.returncode == 125 and not rows, results[-1]
unrelated = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(10)'])
p, rows = run('sleep', '200', 'sleep.lean')
assert unrelated.poll() is None
unrelated.terminate(); unrelated.wait(timeout=2)
assert p.returncode == 124, results[-1]
match = re.search(rb'raw wait status=(\d+); wait errno=(\d+); start ns=(\d+); sample ns=(\d+); limit ms=(\d+)', p.stderr)
assert match and tuple(map(int, match.groups()[:2])) == (9, 0), results[-1]
assert 200000000 <= int(match.group(4)) - int(match.group(3)) < 1500000000, results[-1]
if rows:
    assert rows[0]['wall_timeout'] and rows[0]['raw_wait_status'] == 9, rows
pid = int((work / 'sleep.pid').read_text())
stat = Path(f'/proc/{pid}/stat')
assert not stat.exists() or stat.read_text().split(') ')[1][0] == 'Z', pid
results[-1]['descendant_pid'] = pid
for lease in (work / 'sleep/session').glob('ticket-*'):
    with lease.open('r+') as handle:
        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
p, rows = run('busy', '200', 'busy.lean')
assert p.returncode == 124 and b'raw wait status=9' in p.stderr, results[-1]
# Block or fail record publication after notification; group cleanup still wins.
for mode in ('WALL_SLOW_RECORD', 'WALL_FAIL_RECORD'):
    p, rows = run(mode.lower(), '200', 'busy.lean', mode)
    assert p.returncode == 124 and b'raw wait status=9' in p.stderr, results[-1]
    assert results[-1]['wrapper_seconds'] < 4, results[-1]
    assert (work / (mode.lower() + '.blocked')).exists(), results[-1]
    for lease in (work / mode.lower() / 'session').glob('ticket-*'):
        with lease.open('r+') as handle: fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
# The pinned pidfd fallback carries the cause when the datagram send fails;
# its signal cannot carry physical wait observations, which remain unknown if
# the observer's optional record does not survive cleanup.
p, rows = run('send-failure', '200', 'busy.lean', 'WALL_FAIL_SEND')
assert p.returncode == 124 and b'compiler wall deadline exceeded' in p.stderr, results[-1]
assert results[-1]['wrapper_seconds'] < 4, results[-1]
# An actual selected Lean compilation under a generous deadline.
real = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip()) / 'bin/lean'
(work / 'Tiny.lean').write_text('def tiny : Nat := 1\n')
state = work / 'real'
env = os.environ.copy(); env['HEAVY_COMPILER_WALL_MS'] = '5000'; env.pop('HEAVY_COMPILER_CPU_SECONDS', None)
cmd = [str(ENTRY), '--state', str(state), '--real-lean', str(real), '--allowance-kib', '1300000',
       '--headroom-kib', '100000', '--fallback-kib', '600000', '--timeout-ms', '30000', '--requests', str(request),
       '--', sys.executable, '-c', 'import os,subprocess,sys; sys.exit(subprocess.call([os.environ["LEAN_SYSROOT"]+"/bin/lean", "Tiny.lean"]))']
t = time.monotonic(); p = subprocess.run(cmd, env=env, cwd=work, capture_output=True, timeout=10)
rows = [json.loads(f.read_text()) for f in (state / 'overlay/records').glob('process-*.json')]
results.append(dict(case='real-lean', status=p.returncode, wrapper_seconds=time.monotonic()-t, records=rows, stdout=p.stdout.decode(), stderr=p.stderr.decode()))
assert p.returncode == 0 and len(rows) == 1 and rows[0]['compiler_wall_applied_ms'] == 5000 and rows[0]['raw_wait_status'] == 0, results[-1]
# Remove the configured compiler after overlay setup. Preserve physical exec
# failure instead of mistaking it for a deadline.
missing = work / 'missing/bin/lean'; missing.parent.mkdir(parents=True); shutil.copy2(fixture, missing)
state = work / 'exec-failure'
env = os.environ.copy(); env['HEAVY_COMPILER_WALL_MS'] = '2000'; env.pop('HEAVY_COMPILER_CPU_SECONDS', None)
driver = 'import os,subprocess,sys; os.unlink(sys.argv[1]); sys.exit(subprocess.call([os.environ["LEAN_SYSROOT"]+"/bin/lean", "bad.lean"]))'
cmd = [str(ENTRY), '--state', str(state), '--real-lean', str(missing), '--allowance-kib', '1300000',
       '--headroom-kib', '100000', '--fallback-kib', '600000', '--timeout-ms', '30000', '--requests', str(request),
       '--', sys.executable, '-c', driver, str(missing)]
t = time.monotonic(); p = subprocess.run(cmd, env=env, cwd=work, capture_output=True, timeout=8)
rows = [json.loads(f.read_text()) for f in (state / 'overlay/records').glob('process-*.json')]
results.append(dict(case='exec-failure', status=p.returncode, wrapper_seconds=time.monotonic()-t, records=rows,
                    stdout=p.stdout.decode(), stderr=p.stderr.decode()))
assert p.returncode == 127 and rows[0]['exec_errno'] == 2 and not rows[0]['wall_timeout'], results[-1]
# The first compiler holds the only fitting reservation; the second has a
# shorter deadline but completes after admission. Its wait must not count.
state = work / 'admission'
env = os.environ.copy(); env.pop('HEAVY_COMPILER_CPU_SECONDS', None)
env['HEAVY_COMPILER_WALL_MS'] = '2000'
driver = r"""import os, subprocess, time
lean = os.environ['LEAN_SYSROOT'] + '/bin/lean'
a = subprocess.Popen([lean, 'hold.lean'])
time.sleep(.2)
e = dict(os.environ, HEAVY_COMPILER_WALL_MS='300')
b = subprocess.Popen([lean, 'ok.lean'], env=e)
assert a.wait() == 0 and b.wait() == 0
"""
cmd = [str(ENTRY), '--state', str(state), '--real-lean', str(fixture), '--allowance-kib', '1300000',
       '--headroom-kib', '100000', '--fallback-kib', '700000', '--timeout-ms', '30000', '--requests', str(request),
       '--', sys.executable, '-c', driver]
t = time.monotonic(); p = subprocess.run(cmd, env=env, cwd=work, capture_output=True, timeout=8)
rows = [json.loads(f.read_text()) for f in (state / 'overlay/records').glob('process-*.json')]
results.append(dict(case='admission', status=p.returncode, wrapper_seconds=time.monotonic()-t, records=rows,
                    stdout=p.stdout.decode(), stderr=p.stderr.decode()))
second = next(r for r in rows if r['source'] == 'ok.lean')
assert p.returncode == 0 and second['admission_wait_ns'] > 300000000 and not second['wall_timeout'], results[-1]
assert second['wall_ns'] < 300000000, second
(work / 'results.json').write_text(json.dumps(results, indent=2))
print(work)
