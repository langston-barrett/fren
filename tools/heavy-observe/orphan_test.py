"""Kernel-checked exited-orphan and foreign-child controls for OwnedRun.

The fixture knows exact fork/Popen children independently of the runner. It
never accepts the runner's own empty remaining list as proof of reaping.
"""
import ast
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

from owned_test import run as owned_run


def state(pid):
    raw = Path(f'/proc/{pid}/stat').read_text()
    fields = raw[raw.rfind(')') + 2:].split()
    return dict(pid=pid, state=fields[0], ppid=int(fields[1]), start=int(fields[19]))


def children():
    # Independent of OwnedRun's marker scan, handles and completion fields.
    result = set()
    for task in Path('/proc/self/task').iterdir():
        result.update(map(int, (task / 'children').read_text().split()))
    return result


def consumer_controls(work, env, unknown, failed):
    """Bind the actual direct success guard to actual IO outcomes.

    Zero root status cannot establish cleanup. This is a Python consumer
    regression, not a numerical model or another Lake/compiler workload.
    """
    source = Path(__file__).resolve().parents[2] / 'scripts/heavy_build_test.py'
    text = source.read_text()
    function = next(n for n in ast.parse(text).body
                    if isinstance(n, ast.FunctionDef) and n.name == 'review_fixes')
    call, = [n for n in ast.walk(function) if isinstance(n, ast.Assign)
             and isinstance(n.value, ast.Call) and isinstance(n.value.func, ast.Name)
             and n.value.func.id == 'run' and n.value.args
             and isinstance(n.value.args[0], ast.Constant)
             and n.value.args[0].value == 'existing-target-route']
    guard, = [n for n in ast.walk(function) if isinstance(n, ast.Assert)
              and n.lineno == call.end_lineno + 1]
    code = compile(ast.Expression(guard.test), str(source), 'eval')
    p = owned_run([sys.executable, '-I', '-c',
                   'print("consumer stdout"); __import__("sys").stderr.write("consumer stderr\\n")'],
                  directory=work, label='consumer-success', env=env, timeout=2, check=True)
    positive = json.loads((work / 'consumer-success.json').read_text())
    assert (p.returncode, p.stdout, p.stderr) == (0, b'consumer stdout\n', b'consumer stderr\n')
    assert positive['physical_status_known'] and positive['root_wait_observation']['raw_wait_status'] == 0
    assert positive['cleanup']['outcome'] == 'complete' and positive['product_success']
    assert unknown['physical_status_known'] and unknown['status'] == 0 and unknown['failure'] is None
    assert unknown['cleanup']['outcome'] == 'unknown' and not unknown['product_success']
    assert failed['status'] == 7 and failed['cleanup']['outcome'] == 'complete'
    decisions = [eval(code, {'row': row}) for row in (unknown, failed, positive)]
    assert decisions == [False, False, True], decisions
    result = dict(source=str(source), source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  line=guard.lineno, predicate=ast.get_source_segment(text, guard.test),
                  outcomes=['successful-root/unknown-cleanup', 'exit7/complete', 'exit0/complete'],
                  accepts=decisions, rows=[unknown, failed, positive])
    (work / 'consumer-result.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def controls(work, env):
    worker = work / 'early-orphan.py'
    worker.write_text(r'''
import json,os,sys,time
from pathlib import Path
pid=os.fork()
if pid==0: os._exit(17)
# WNOWAIT establishes an already-exited exact fork child without consuming it.
observed=os.waitid(os.P_PID,pid,os.WEXITED|os.WNOWAIT)
raw=Path(f'/proc/{pid}/stat').read_text();fields=raw[raw.rfind(')')+2:].split()
Path(sys.argv[1]).write_text(json.dumps({'pid':pid,'start':int(fields[19]),'wait_pid':observed.si_pid,'exit_status':observed.si_status}))
print('orphan-parent stdout',flush=True)
print('orphan-parent stderr',file=sys.stderr,flush=True)
time.sleep(.1)
''')
    marker = work / 'early-orphan.ready'
    orphan = None
    orphan_reaped = False
    result = {}
    try:
        try:
            owned_run([sys.executable, '-I', str(worker), str(marker)], directory=work,
                      label='early-orphan', env=env, timeout=2, grace=.1)
        except RuntimeError as error:
            result['adapter_error'] = str(error)
            assert 'owned cleanup unestablished' in str(error), error
        else:
            raise AssertionError('unattributed exited child was certified complete')
        orphan = json.loads(marker.read_text())
        observed = state(orphan['pid'])
        assert orphan['wait_pid'] == orphan['pid'] and orphan['exit_status'] == 17
        assert observed['start'] == orphan['start'] and observed['state'] == 'Z'
        assert observed['ppid'] == os.getpid() and orphan['pid'] in children(), observed
        receipt = json.loads((work / 'early-orphan.json').read_text())
        assert receipt['physical_status'] == 0 and receipt['physical_status_known']
        assert receipt['cleanup']['outcome'] == 'unknown' and not receipt['product_success']
        assert any(r['pid'] == orphan['pid'] and r['start'] == orphan['start']
                   for r in receipt['cleanup']['unattributed_children']), receipt
        assert (work / 'early-orphan.stdout').read_bytes() == b'orphan-parent stdout\n'
        assert (work / 'early-orphan.stderr').read_bytes() == b'orphan-parent stderr\n'
        # Only this fixture has independent provenance for that exact fork.
        # Reap it explicitly; no blanket wait and no signal to an unknown child.
        reaped = os.waitpid(orphan['pid'], os.WNOHANG)
        assert reaped == (orphan['pid'], 17 << 8), reaped
        assert orphan['pid'] not in children()
        result.update(orphan=orphan, kernel_before_reap=observed,
                      exact_fixture_reap=list(reaped), receipt=receipt)
        orphan_reaped = True
    finally:
        if not orphan_reaped and orphan is None and marker.exists():
            orphan = json.loads(marker.read_text())
        if not orphan_reaped and orphan is not None:
            try:
                remaining = state(orphan['pid'])
                if remaining['ppid'] == os.getpid() and remaining['start'] == orphan['start'] and remaining['state'] == 'Z':
                    os.waitpid(orphan['pid'], os.WNOHANG)
            except (FileNotFoundError, ProcessLookupError, ChildProcessError):
                pass

    # Baseline foreign children must not be consumed or signalled. One is live;
    # one is a zombie with no usable environment, both created before the run.
    live = subprocess.Popen([sys.executable, '-I', '-c', 'import time; time.sleep(10)'])
    exited, live_fd = None, None
    try:
        live_fd = os.pidfd_open(live.pid)
        exited = subprocess.Popen([sys.executable, '-I', '-c', 'import os; os._exit(23)'])
        deadline = time.monotonic() + 2
        while state(exited.pid)['state'] != 'Z' and time.monotonic() < deadline:
            time.sleep(.01)
        before = state(exited.pid); live_before = state(live.pid)
        assert before['state'] == 'Z' and {live.pid, exited.pid} <= children()
        p = owned_run([sys.executable, '-I', '-c',
                       'import sys; print("status stdout"); print("status stderr",file=sys.stderr); sys.exit(7)'],
                      directory=work, label='foreign-preservation', env=env, timeout=2, grace=.1)
        assert (p.returncode, p.stdout, p.stderr) == (7, b'status stdout\n', b'status stderr\n')
        assert live.poll() is None and state(live.pid)['start'] == live_before['start']
        after = state(exited.pid)
        assert after == before and exited.pid in children(), (before, after)
        reaped = os.waitpid(exited.pid, os.WNOHANG)
        assert reaped == (exited.pid, 23 << 8), reaped
        exited.returncode = 23
        receipt = json.loads((work / 'foreign-preservation.json').read_text())
        assert receipt['cleanup']['outcome'] == 'complete'
        assert [before['pid'], before['start']] in receipt['cleanup']['preexisting_children']
        result['foreign'] = dict(before=before, after=after, exact_fixture_reap=list(reaped),
                                 live_before=live_before, live_after=state(live.pid), receipt=receipt)
    finally:
        try:
            if exited is not None and exited.returncode is None:
                exited.wait(timeout=2)  # Exact Popen child; never another caller's.
        finally:
            # live is this fixture's exact, unreaped Popen child. Even a
            # pidfd-open failure must not skip its bounded cleanup.
            def stop(sig):
                try:
                    if live_fd is None:
                        live.send_signal(sig)
                    else:
                        signal.pidfd_send_signal(live_fd, sig)
                except ProcessLookupError:
                    pass
            try:
                stop(signal.SIGTERM)
                try:
                    live.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    stop(signal.SIGKILL)
                    live.wait(timeout=2)
            finally:
                if live_fd is not None:
                    os.close(live_fd)
    result['consumer'] = consumer_controls(work, env, result['receipt'], result['foreign']['receipt'])
    (work / 'orphan-result.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def status_controls(work, env):
    """Actual raw waits under ordinary, ignored and native auto-reap policy.

    Each policy lives in a dedicated fixture process. A tiny C test shim uses
    this platform's sigaction headers; no Python struct layout or production
    ABI is assumed. It only sets/reads/restores that fixture's own policy.
    """
    source = work / 'sigchld.c'
    library = work / 'sigchld.so'
    source.write_text(r'''
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
static struct sigaction saved;
int no_wait_mask(void) { return SA_NOCLDWAIT; }
int begin_no_wait(void) {
  if (sigaction(SIGCHLD, 0, &saved)) return errno;
  struct sigaction action = saved;
  action.sa_flags |= SA_NOCLDWAIT;
  return sigaction(SIGCHLD, &action, 0) ? errno : 0;
}
int restore_policy(void) { return sigaction(SIGCHLD, &saved, 0) ? errno : 0; }
int current_flags(void) {
  struct sigaction action;
  return sigaction(SIGCHLD, 0, &action) ? -1 : action.sa_flags;
}
int current_disposition(void) {
  struct sigaction action;
  if (sigaction(SIGCHLD, 0, &action)) return -1;
  return action.sa_handler == SIG_DFL ? 0 : action.sa_handler == SIG_IGN ? 1 : 2;
}
int current_mask(int sig) {
  struct sigaction action;
  return sigaction(SIGCHLD, 0, &action) ? -1 : sigismember(&action.sa_mask, sig);
}
''')
    owned_run(['cc', '-shared', '-fPIC', str(source), '-o', str(library)],
              directory=work, label='sigchld-shim', env=env, timeout=3, check=True)
    worker = work / 'status-worker.py'
    worker.write_text('import sys\nsys.path.insert(0,' + repr(str(Path(__file__).resolve().parent)) + ')\n' + r'''
import ctypes,errno,json,os,signal,time
from pathlib import Path
from owned_test import run
work=Path(sys.argv[1]);mode=sys.argv[2];lib=ctypes.CDLL(sys.argv[3])
def policy():
 return dict(python_disposition=int(signal.getsignal(signal.SIGCHLD)),
             flags=lib.current_flags(),disposition=lib.current_disposition(),
             mask=[lib.current_mask(sig) for sig in range(1,signal.NSIG)])
original=policy();previous=signal.getsignal(signal.SIGCHLD)
assert previous==signal.SIG_DFL and original['disposition']==0,original
ready=work/(mode+'.ready');stolen=[]
body='import os,pathlib,sys; print("actual exit 7 stdout",flush=True); print("actual exit 7 stderr",file=sys.stderr,flush=True); pathlib.Path(sys.argv[1]).write_text("{}"); \nif sys.argv[2]=="lost-status":\n import time\n deadline=time.monotonic()+2\n while not pathlib.Path(sys.argv[1]+".release").exists() and time.monotonic()<deadline: time.sleep(.005)\nsys.exit(7)'
def steal(owner,process,data):
 Path(str(ready)+'.release').write_text('exact fixture releases root exit')
 deadline=time.monotonic()+1
 while time.monotonic()<deadline:
  observed=os.waitpid(process.pid,os.WNOHANG)
  if observed[0]: stolen.append(list(observed));return
  time.sleep(.005)
 raise AssertionError('exact fixture wait did not complete')
result=dict(mode=mode,original_policy=original,stolen=stolen)
try:
 if mode=='ignored': signal.signal(signal.SIGCHLD,signal.SIG_IGN)
 if mode=='no-child-wait': assert lib.begin_no_wait()==0
 before=policy()
 if mode=='ignored': assert before['disposition']==1
 if mode=='no-child-wait':
  assert before['flags'] & lib.no_wait_mask() and before['disposition']==0,before
 try:
  p=run([sys.executable,'-I','-c',body,str(ready),mode],directory=work,label=mode,
        timeout=1,grace=.1,ready=ready if mode=='lost-status' else None,
        action=steal if mode=='lost-status' else None)
  result['returned_status']=p.returncode
 except RuntimeError as error:
  result['adapter_error']=str(error)
 after=policy()
 assert before==after,(before,after)
 result.update(policy_before=before,policy_after=after)
finally:
 if mode=='ignored': signal.signal(signal.SIGCHLD,previous)
 if mode=='no-child-wait': assert lib.restore_policy()==0
restored=policy();result['restored_policy']=restored
assert signal.getsignal(signal.SIGCHLD)==previous
assert restored['disposition']==original['disposition'] and restored['mask']==original['mask']
assert restored['flags'] & lib.no_wait_mask()==original['flags'] & lib.no_wait_mask()
row=json.loads((work/(mode+'.json')).read_text());result['receipt']=row
assert (work/(mode+'.stdout')).read_bytes()==b'actual exit 7 stdout\n'
assert (work/(mode+'.stderr')).read_bytes()==b'actual exit 7 stderr\n'
if mode=='normal':
 assert result['returned_status']==row['physical_status']==7 and row['physical_status_known'],result
 assert row['root_wait_observation']==dict(pid=row['root_pid'],raw_wait_status=7<<8,status=7),row
 assert row['root_wait_errno'] is None and row['cleanup']['outcome']=='complete'
else:
 assert 'adapter_error' in result and 'returned_status' not in result,result
 assert row['physical_status'] is None and not row['physical_status_known']
 assert row['root_wait_observation'] is None and row['root_wait_errno']==errno.ECHILD,row
 assert row['cleanup']['outcome']=='unknown' and not row['product_success'],row
 if mode=='lost-status': assert stolen==[[row['root_pid'],7<<8]],result
result['kernel_children_after']={p.name:(p/'children').read_text().split() for p in Path('/proc/self/task').iterdir()}
assert all(not pids for pids in result['kernel_children_after'].values()),result
(work/(mode+'-result.json')).write_text(json.dumps(result,indent=2)+'\n')
''')
    results = []
    for mode in ('normal', 'ignored', 'no-child-wait', 'lost-status'):
        owned_run([sys.executable, '-I', str(worker), str(work), mode, str(library)],
                  directory=work, label=mode + '-worker', env=env, timeout=3, grace=.1, check=True)
        results.append(json.loads((work / (mode + '-result.json')).read_text()))
    (work / 'status-result.json').write_text(json.dumps(results, indent=2) + '\n')
    return results
