#!/usr/bin/env python3
"""Bounded ordinary Heavy dispatch controls using the real session controller.

Run under Heavy offline with prebuilt heavy_observe/budget_session. All nested
Heavy instances use private test state. --output retains source/status/timings.
The one existing-target compilation is a separate explicit validation command.
"""
import argparse
import hashlib
import importlib.machinery
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import traceback
from unittest import mock

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
HEAVY = ROOT / 'scripts/heavy'


def load(path):
    loader = importlib.machinery.SourceFileLoader(path.name.replace('-', '_'), str(path))
    spec = importlib.util.spec_from_loader(loader.name, loader)
    module = importlib.util.module_from_spec(spec)
    loader.exec_module(module)
    return module


class OwnedRun:
    """Finite fixture IO: nonce inheritance identifies only our test workers.

    Capture a stable pidfd between matching procfs reads before signalling.
    The nonce is fresh per run and never given to unrelated survivor controls.
    Same-user hostile environment mutation is outside this test boundary.
    """
    def __init__(self, heavy, directory, label):
        self.heavy, self.directory, self.label = heavy, directory, label
        self.token = os.urandom(24).hex()
        self.handles = {}
        self.errors = []
        self.cancelled = None

    def collect(self):
        marker = ('HEAVY_TEST_OWNER=' + self.token).encode()
        inherited = ('HEAVY_TEST_OWNED_' + self.token + '=1').encode()
        rows = {}
        for name in os.listdir('/proc'):
            if not name.isdigit():
                continue
            try:
                path = Path('/proc') / name
                environment = (path / 'environ').read_bytes().split(b'\0')
                if marker not in environment and inherited not in environment:
                    continue
                row = self.heavy.process_stat((path / 'stat').read_text())
                key = row['pid'], row['start']
                if key not in self.handles:
                    fd = os.pidfd_open(row['pid'])
                    try:
                        after = self.heavy.process_stat((path / 'stat').read_text())
                        pinned = next(int(s.split()[1]) for s in Path(f'/proc/self/fdinfo/{fd}').read_text().splitlines()
                                      if s.startswith('Pid:'))
                        if (after['pid'], after['start'], pinned) != (*key, key[0]):
                            continue
                        self.handles[key] = fd
                        fd = None
                    finally:
                        if fd is not None:
                            os.close(fd)
                rows[key] = row
            except (FileNotFoundError, ProcessLookupError, PermissionError):
                continue
        # Previously pinned workers remain ours after exit clears environ.
        # Retain their zombies until an owned nonblocking wait reaps them.
        for key, fd in self.handles.items():
            try:
                row = self.heavy.process_stat(Path(f'/proc/{key[0]}/stat').read_text())
                pinned = next(int(s.split()[1]) for s in Path(f'/proc/self/fdinfo/{fd}').read_text().splitlines()
                              if s.startswith('Pid:'))
                if (row['pid'], row['start'], pinned) == (*key, key[0]):
                    rows[key] = row
            except (FileNotFoundError, ProcessLookupError):
                pass
        return rows

    def send(self, pid, sig):
        rows = self.collect()
        keys = [k for k in rows if k[0] == pid]
        if len(keys) != 1:
            raise AssertionError(('unverified fixture signal target', pid))
        signal.pidfd_send_signal(self.handles[keys[0]], sig)

    def execute(self, argv, *, cwd, env, ready=None, action=None, timeout=20,
                ready_timeout=15, grace=8, input_data=b'input \xce\xbb\n'):
        start = time.monotonic()
        row = {'case': self.label, 'argv': list(map(str, argv)), 'status': None,
               'physical_status': None, 'failure': None, 'cleanup': {}}
        outpath = self.directory / (self.label + '.stdout')
        errpath = self.directory / (self.label + '.stderr')
        p = None
        # File-backed streams retain partial output even if a writer survives;
        # no communicate() or pipe EOF wait can hide timeout/cleanup evidence.
        with self.heavy.child_subreaper() as subreaper, \
             outpath.open('wb') as stdout, errpath.open('wb') as stderr, \
             tempfile.TemporaryFile() as stdin:
            stdin.write(input_data); stdin.seek(0)
            try:
                assert subreaper, "fixture subreaper unavailable"
                if self.cancelled is not None:
                    raise InterruptedError('owned runner cancelled before launch')
                child_env = dict(env, HEAVY_TEST_OWNER=self.token)
                # Retain ancestor ownership through nested runners even when
                # their private HEAVY_TEST_OWNER changes.
                child_env['HEAVY_TEST_OWNED_' + self.token] = '1'
                p = subprocess.Popen(list(map(str, argv)), cwd=cwd,
                    env=child_env, stdin=stdin,
                    stdout=stdout, stderr=stderr, start_new_session=True)
                self.collect()
                if ready is not None:
                    deadline = time.monotonic() + ready_timeout
                    while not ready.exists() and p.poll() is None and time.monotonic() < deadline:
                        if self.cancelled is not None:
                            raise InterruptedError('owned runner cancelled during readiness')
                        self.collect(); time.sleep(.02)
                    if not ready.exists():
                        raise RuntimeError('readiness failure')
                    if action is not None:
                        action(self, p, json.loads(ready.read_text()))
                deadline = time.monotonic() + timeout
                while p.poll() is None and time.monotonic() < deadline:
                    if self.cancelled is not None:
                        raise InterruptedError('owned runner cancelled')
                    self.collect(); time.sleep(.02)
                if self.cancelled is not None:
                    raise InterruptedError('owned runner cancelled')
                if p.poll() is None:
                    raise TimeoutError('wrapper timeout')
                survivors = [r for r in self.collect().values() if r['state'] not in ('Z', 'X')]
                row['survivors_before_harness_cleanup'] = survivors
                if survivors:
                    raise RuntimeError('fixture workers survived wrapper completion')
            except BaseException as error:
                row['failure'] = repr(error)
                row['failure_traceback'] = traceback.format_exc()
            finally:
                cleanup_start = time.monotonic()
                # All failure paths use the same bounded handle-only cleanup.
                for sig, wait in ((signal.SIGTERM, grace), (signal.SIGKILL, 2)):
                    deadline = time.monotonic() + wait
                    while True:
                        rows = self.collect()
                        for key, fd in self.handles.items():
                            try:
                                signal.pidfd_send_signal(fd, sig)
                            except ProcessLookupError:
                                pass
                            except OSError as error:
                                self.errors.append(str(error))
                        if p is not None:
                            p.poll()
                        for key in self.handles:
                            if p is not None and key[0] == p.pid:
                                continue
                            try:
                                os.waitpid(key[0], os.WNOHANG)
                            except ChildProcessError:
                                pass
                        live = list(self.collect().values())
                        if not live and (p is None or p.returncode is not None):
                            break
                        if time.monotonic() >= deadline:
                            break
                        time.sleep(.02)
                    if not live and (p is None or p.returncode is not None):
                        break
                row.update(status=None if p is None else p.returncode,
                           physical_status=None if p is None else p.returncode,
                           physical_status_known=p is not None and p.returncode is not None,
                           wrapper_wall_seconds=time.monotonic() - start,
                           stdout=str(outpath), stderr=str(errpath))
                row['cleanup'] = {'outcome': 'complete' if not live and (p is None or p.returncode is not None) else 'failed',
                                  'seconds': time.monotonic() - cleanup_start,
                                  'remaining': live, 'errors': self.errors}
                row['product_success'] = row['failure'] is None and row['physical_status'] == 0 and row['cleanup']['outcome'] == 'complete'
                for fd in self.handles.values():
                    os.close(fd)
                self.handles.clear()
                stdout.flush(); stderr.flush()
                (self.directory / (self.label + '.json')).write_text(json.dumps(row, indent=2) + '\n')
        return row, outpath.read_bytes(), errpath.read_bytes()


def review_fixes(work, family_only=False):
    heavy, build = load(HEAVY), load(ROOT / 'scripts/fren-build')
    real = Path('/opt/elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
    tools = ROOT / 'tools/heavy-observe'
    ordinary = work / 'ordinary'; ordinary.mkdir()
    (ordinary / 'lakefile.toml').write_text('name = "routing_ordinary"\ndefaultTargets = ["ordinary_marker"]\n')
    (ordinary / 'alternate.toml').write_text('name = "routing_alternate"\ndefaultTargets = ["alternate_marker"]\n')
    env = dict(os.environ, HOME=str(work / 'home'), TMPDIR=str(work),
               HEAVY_MEM_GB='1.5', HEAVY_SLOTS='1', HEAVY_MAX_LOAD='off',
               PYTHONDONTWRITEBYTECODE='1')
    for name in ('HEAVY_BUDGET_DIR','LEAN_SYSROOT','LAKE_OVERRIDE_LEAN','HEAVY_OBSERVE_DIR',
                 'FREN_BUILD_REQUESTS_FILE','FREN_BUILD_ALLOWANCE_KIB','FREN_BUILD_HEADROOM_KIB',
                 'FREN_BUILD_FALLBACK_KIB','FREN_BUILD_TIMEOUT_MS','HEAVY_LOG'):
        env.pop(name, None)
    cases = []
    def run(label, command, **kwargs):
        owner = OwnedRun(heavy, work, label)
        row, stdout, stderr = owner.execute(command, cwd=ROOT, env=kwargs.pop('env', env), **kwargs)
        cases.append(row)
        (work / 'results.json').write_text(json.dumps(cases, indent=2) + '\n')
        return row, stdout, stderr

    if not family_only:
        # Both directions, all accepted -d/--dir forms, repeated options, alternate
        # configs, empty leading argv, argument insertion and Lake's subArgs stop.
        spellings = lambda path: [['-d',str(path)], ['-d='+str(path)], ['-d'+str(path)],
            ['--dir',str(path)], ['--dir='+str(path)], ['--dir '+str(path)], ['-d '+str(path)]]
        decisions = []
        for before, after, expect in ((tools, ordinary, True),(ordinary, tools,False)):
            for form in spellings(after):
                argv=['lake','-d',str(before),'build',*form]
                result=build.heavy_command(argv, 1572864)
                assert (result != argv) == expect, argv
                decisions.append({'argv':argv,'gated':result != argv})
        for argv, expect in [
            (['lake','','build'],True),
            (['lake','--dir '+str(tools),'build'],False),
            (['lake','build','--dir',str(tools),'-f','other.lean'],True),
            (['lake','build','--dir',str(tools),'--file=lakefile.lean'],False),
            (['lake','build','--dir',str(tools),'-f '+str(ordinary/'alternate.toml')],True),
            (['lake','build','--dir',str(ordinary),'Target','--','--dir',str(tools)],True),
            (['lake','-d',str(tools),'build','--','--dir',str(ordinary)],False),
            (['lake','--','build'],False),
            (['lake','env','build'],False),
            (['lake','build','--help'],False),
            (['lake','build','Target','--help'],True),
            (['lake','--quiet=build','--dir',str(ordinary)],True)]:
            assert (build.heavy_command(argv,1572864) != argv) == expect,argv
            decisions.append({'argv':argv,'gated':expect})
        (work/'routing-decisions.json').write_text(json.dumps(decisions,indent=2)+'\n')
        try:
            build.heavy_command(['lake','--unrecognized','build'],1572864)
            raise AssertionError('unknown grammar bypassed')
        except ValueError:
            pass
        native=real.parent/'lake'
        # Actual pinned Lake witnesses: owned TOML configs contain distinct missing
        # default-target markers. These load configs but compile no modules.
        for label, argv, marker, gated in [
            ('route-out-of-tools',['-d',str(tools),'build','--dir',str(ordinary)],b'ordinary_marker',True),
            ('route-empty',['','build','--dir '+str(ordinary)],b'ordinary_marker',True),
            ('route-file',['build','-d '+str(ordinary),'--file alternate.toml'],b'alternate_marker',True),
            ('route-after-stop',['-d',str(ordinary),'build','--','--dir',str(tools)],b'ordinary_marker',True),
            ('route-into-tools',['-d',str(ordinary),'build','--dir='+str(tools),'budget_session','--no-build'],None,False)]:
            before=set(work.glob('fren-build-*'))
            row,stdout,stderr=run(label,[HEAVY,'--offline',native,*argv,'--offline','--no-cache'])
            assert not row['failure'] and row['cleanup']['outcome']=='complete',row
            assert bool(set(work.glob('fren-build-*'))-before)==gated,(label,stderr)
            if marker:
                assert row['status'] != 0 and marker in stdout+stderr,(label,row,stdout,stderr)
            else:
                assert row['status']==0,(row,stdout,stderr)
        # Existing target at the corrected cross-verb path, cached and --no-build:
        # this validates routing without recompiling unchanged Lean for a new SHA.
        row,stdout,stderr=run('existing-target-route',[HEAVY,'--offline',native,'-d',str(tools),
            'build','--dir',str(ROOT),'+Heavy.Process:olean','--no-build','--offline','--no-cache'])
        assert row['status']==0 and not row['failure'],(row,stdout,stderr)

    fake=work/'bin';fake.mkdir();(fake/'lean').symlink_to(real)
    lake=fake/'lake'
    lake.write_text('#!'+sys.executable+'\n'+r'''
import json,os,pathlib,subprocess,sys,time
size = int(os.environ.get('HELPER_BYTES','1024'))
child=subprocess.Popen([sys.executable,'-c',
 'import os,pathlib,sys,time; x=bytearray(int(sys.argv[1])); '
 'pathlib.Path(sys.argv[2]).write_text(str(os.getpid())); '
 'print("helper-partial",flush=True); time.sleep(20)',str(size),os.environ['HELPER_READY']])
limit=time.monotonic()+4
while not pathlib.Path(os.environ['HELPER_READY']).exists() and time.monotonic()<limit:time.sleep(.01)
pathlib.Path(os.environ['READY']).write_text(json.dumps({'controller':os.getppid(),'lake':os.getpid(),'helper':child.pid}))
print('lake-partial',flush=True)
sys.exit(child.wait())
''');lake.chmod(0o755)
    # Actual fault injection occurs only after the real controller/Lake/helper
    # exist. Faults select existing cleanup callers, not a substitute supervisor.
    launcher=work/'fault.py'
    launcher.write_text(r'''
import json,os,pathlib,runpy,sys,time
m=runpy.run_path(sys.argv[1]);mode=sys.argv[2];ready=pathlib.Path(os.environ['READY']);trigger=pathlib.Path(os.environ['TRIGGER'])
def rendezvous():
 deadline=time.monotonic()+6
 while not trigger.exists() and time.monotonic()<deadline:time.sleep(.01)
 if not trigger.exists():raise OSError('fault rendezvous failed')
def fail(*args,**kwargs):rendezvous();raise OSError('injected '+mode)
if mode=='identify':m['visible_group'].__globals__['visible_group']=fail
if mode=='account':m['publish_memory'].__globals__['publish_memory']=fail
if mode=='census':
 cls=m['ControlledSession']; original=cls.observe
 def missed(self):
  rows=original(self)
  if self.exited and self.child.returncode is None:
   return {k:r for k,r in rows.items() if r['pid']==self.child.pid}
  return rows
 cls.observe=missed
if mode=='shared':
 original=m['memory_victim']
 def victim(rows,cap):
  rendezvous()
  own=[r for r in rows if r.get('job_id')]
  assert len(own)==1
  return cap+1,own[0]['job_id']
 original.__globals__['memory_victim']=victim
if mode=='status':
 m['write_status'].__globals__['write_status']=fail
 import tempfile
 state=os.environ['TEST_STATE'];pathlib.Path(state).mkdir()
 record={'compiler_budget':True,'started_at':time.time()}
 command=runpy.run_path(str(pathlib.Path(sys.argv[1]).with_name('fren-build')))['heavy_command'](sys.argv[3:],1572864)
 with open(pathlib.Path(state)/'legacy-slot','a+') as f:
  status=m['run'](f,command,'fixture status failure','fixture',record,time.monotonic(),state,os.environ,lambda:0)
 pathlib.Path(os.environ['FAULT_RECORD']).write_text(json.dumps(record))
 sys.exit(status)
sys.exit(m['main'](['--offline',*sys.argv[3:]],state=os.environ['TEST_STATE']))
''')
    # An unrelated direct child stays alive across every production cleanup.
    survivor=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)'])
    survivor_fd=os.pidfd_open(survivor.pid)
    survivor_report={'before':heavy.process_stat(Path(f'/proc/{survivor.pid}/stat').read_text()),'after_cases':[]}
    try:
        for mode in ('cancel','identify','status','account','local','shared','census'):
            label='family-'+mode;ready=work/(label+'.ready');trigger=work/(label+'.trigger')
            local=dict(env,READY=str(ready),TRIGGER=str(trigger),HELPER_READY=str(work/(label+'.helper')),
                TEST_STATE=str(work/(label+'-state')),FAULT_RECORD=str(work/(label+'.record.json')),
                HOME=str(work/(label+'-home')))
            if mode=='local':
                local.update(HEAVY_MEM_GB='.2',FREN_BUILD_HEADROOM_KIB='1000',FREN_BUILD_FALLBACK_KIB='1000',HELPER_BYTES=str(224*1024*1024))
            def action(owner,process,ids):
                rows=owner.collect();by_pid={r['pid']:r for r in rows.values()}
                controller,command,helper=(by_pid[ids[k]] for k in ('controller','lake','helper'))
                assert command['ppid']==controller['pid'] and helper['ppid']==command['pid']
                assert controller['session']==command['session']==helper['session']
                assert command['pgrp']==helper['pgrp']!=controller['pgrp']
                (work/(label+'.identities.json')).write_text(json.dumps(by_pid,indent=2)+'\n')
                owner.send(controller['pid'],signal.SIGKILL if mode=='census' else signal.SIGSTOP)
                trigger.write_text('trigger')
                if mode=='cancel':
                    owner.send(process.pid,signal.SIGTERM)
                    owner.send(process.pid,signal.SIGTERM)
                if mode not in ('status','account','census'):
                    state=(Path(local['HOME'])/'.cache/heavy' if mode in ('cancel','local') else Path(local['TEST_STATE']))
                    samples=[]
                    time.sleep(1.25)
                    for _ in range(2):
                        samples.append(json.loads((state/'.slot0.json').read_text()))
                        time.sleep(.25)
                    assert samples[1]['updated_monotonic']>samples[0]['updated_monotonic']
                    (work/(label+'.cleanup-publications.json')).write_text(json.dumps(samples,indent=2)+'\n')
            argv=([HEAVY,'--offline',lake,'build'] if mode in ('cancel','local') else
                  [sys.executable,'-I',launcher,HEAVY,mode,lake,'build'])
            row,stdout,stderr=run(label,argv,env=local,ready=ready,action=action,timeout=12)
            assert not row['failure'] and row['cleanup']['outcome']=='complete',(mode,row,stderr)
            assert survivor.poll() is None,'unrelated job was signalled'
            observed=heavy.process_stat(Path(f'/proc/{survivor.pid}/stat').read_text())
            assert observed['start']==survivor_report['before']['start']
            survivor_report['after_cases'].append({'case':label,'identity':observed})
            (work/'unrelated-survivor.json').write_text(json.dumps(survivor_report,indent=2)+'\n')
            expected=137 if mode in ('cancel','local','shared','census') else 125
            assert row['status']==expected,(mode,row,stderr)
            assert b'helper-partial' in stdout and b'lake-partial' in stdout
            if mode=='status':
                record=json.loads(Path(local['FAULT_RECORD']).read_text())
            else:
                state=Path(local['TEST_STATE']) if mode not in ('cancel','local') else Path(local['HOME'])/'.cache/heavy'
                record=json.loads((state/'log.jsonl').read_text().splitlines()[-1])
            assert record['controlled_cleanup']['outcome']=='complete',record
            if mode != 'census':
                assert record['controlled_cleanup']['signals'].get('9',0)>0,record
            assert record['command_observed_status']==137,record
            if mode != 'status':
                assert heavy.jobs(str(state))==[]
            (work/(label+'.heavy-record.json')).write_text(json.dumps(record,indent=2)+'\n')
    finally:
        signal.pidfd_send_signal(survivor_fd,signal.SIGTERM)
        survivor_report['physical_final_status']=survivor.wait(timeout=2)
        survivor_report['pinned_pid_after_reap']=next(int(s.split()[1]) for s in Path(f'/proc/self/fdinfo/{survivor_fd}').read_text().splitlines() if s.startswith('Pid:'))
        os.close(survivor_fd)
        (work/'unrelated-survivor.json').write_text(json.dumps(survivor_report,indent=2)+'\n')

    if not family_only:
        # Real harness negatives: partial streams and physical statuses survive
        # readiness/timeout/TERM-resistant paths. Their wrapper status is not a pass.
        for label,body,ready_timeout,timeout in [
            ('harness-orphan','import subprocess,sys; subprocess.Popen([sys.executable,"-c","import time; time.sleep(20)"]); print("partial-orphan",flush=True)',None,1),
            ('harness-early-exit','print("partial-exit",flush=True); __import__("sys").exit(7)',.2,1),
            ('harness-readiness','print("partial-ready",flush=True); __import__("time").sleep(20)',.2,1),
            ('harness-timeout','import signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); print("partial-timeout",flush=True); time.sleep(20)',None,.2)]:
            ready=work/(label+'.never') if ready_timeout is not None else None
            row,stdout,stderr=run(label,[sys.executable,'-c',body],ready=ready,
                ready_timeout=.2,timeout=timeout,grace=.2)
            assert row['failure'] and row['cleanup']['outcome']=='complete',row
            assert stdout.startswith(b'partial-') and row['physical_status'] in (0,7,-15,-9),row
            assert not row['product_success']
        row,stdout,stderr=run('harness-launch-failure',[work/'absent-executable'])
        assert row['failure'] and row['physical_status'] is None and not row['physical_status_known']
        assert row['cleanup']['outcome']=='complete' and not row['product_success']

    (work/'report.json').write_text(json.dumps({'status':'passed','cases':len(cases),
        'meaning':'expected physical outcomes asserted individually; negative harness/reproduction wrapper zero is not product success'},indent=2)+'\n')
    print(f'review-fix controls passed: {work}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--review-fixes', action='store_true')
    parser.add_argument('--family-only', action='store_true')
    args = parser.parse_args()
    work = args.output
    assert work.is_absolute()
    work.mkdir(mode=0o700)
    if args.review_fixes:
        return review_fixes(work, args.family_only)
    results = []
    build = load(ROOT / 'scripts/fren-build')
    heavy = load(HEAVY)
    real = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip()) / 'bin/lean'
    real = real.resolve(strict=True)
    pin = (ROOT / 'lean-toolchain').read_text().strip()
    # Discovery and dispatch use raw argv, not shell text or substring matches.
    for command in (['lake', 'build'], ['lake', '--no-cache', 'build', 'space target'],
                    ['lake', '-d', str(work), 'build'], ['lake', '-K', 'build', 'build'],
                    ['lake', '+' + pin, 'build']):
        assert build.lake_build(command) is not None, command
    for command in (['lake', 'env', 'build'], ['lake', '-d', 'build', 'env'],
                    ['lake', '--help', 'build'], ['lake', '-o', 'build', 'env'],
                    ['lake', '--service', 'build', 'env'], ['echo', 'lake', 'build']):
        assert build.lake_build(command) is None, command
    boot = ['lake', '-d', str(ROOT / 'tools/heavy-observe'), 'build', 'budget_session']
    assert build.heavy_command(boot, 1000000) == boot
    assert build.outer_allowance(1000000) <= 900000
    with mock.patch.object(build.Path, 'read_text', return_value='0::/../bad\n'):
        try:
            build.outer_allowance(1000000)
            raise AssertionError('accepted unresolved cgroup')
        except ValueError:
            pass
    # Compute the ceiling from raw ancestor bytes, including a tighter parent.
    def cgroup_text(path, *args, **kwargs):
        if str(path) == '/proc/self/cgroup':
            return '0::/control/job\n'
        return str((500000 if path.parent.name == 'job' else 400000) * 1024)
    with mock.patch.object(build.Path, 'read_text', cgroup_text), \
         mock.patch.object(build.Path, 'is_dir', return_value=True), \
         mock.patch.object(build.Path, 'exists', return_value=True):
        assert build.outer_allowance(2000000) == 300000
    fake = work / 'bin'; fake.mkdir()
    (fake / 'lean').symlink_to(real)
    lake = fake / 'lake'
    lake.write_text('#!' + sys.executable + '\n' + r'''
import json, os, pathlib, signal, subprocess, sys, time
mode = os.environ.get('CONTROL', 'argv')
if mode == 'assert-gated':
    sys.exit(0 if os.environ.get('HEAVY_BUDGET_DIR') else 19)
if mode == 'missing':
    lean = (pathlib.Path(os.environ['LEAN_SYSROOT']) / 'bin/lean'
            if os.environ.get('HEAVY_BUDGET_DIR') else pathlib.Path(__file__).parent / 'lean')
    sys.exit(subprocess.call([str(lean), 'Missing-source.lean']))
if mode == 'signal':
    os.kill(os.getpid(), signal.SIGTERM)
if mode in ('wait', 'memory'):
    size = 224 * 1024 * 1024 if mode == 'memory' else 1024
    child = subprocess.Popen([sys.executable, '-c',
        'import pathlib,sys,time; x=bytearray(int(sys.argv[1])); '
        'pathlib.Path(sys.argv[2]).write_text(str(__import__("os").getpid())); time.sleep(30)',
        str(size), os.environ['READY']])
    sys.exit(child.wait())
print(json.dumps({'argv': sys.argv[1:], 'cwd': os.getcwd(),
    'sentinel': os.environ.get('SENTINEL'), 'stdin': sys.stdin.read(),
    'budget': os.environ.get('HEAVY_BUDGET_DIR'), 'sysroot': os.environ.get('LEAN_SYSROOT'),
    'net': os.readlink('/proc/self/ns/net')}), flush=True)
if mode == 'pipes':
    sys.stdout.write('O' * 131072); sys.stdout.flush()
    sys.stderr.write('E' * 131072); sys.stderr.flush()
sys.exit(int(os.environ.get('STATUS', '0')))
''')
    lake.chmod(0o755)
    env = dict(os.environ, HOME=str(work / 'home'), TMPDIR=str(work),
               ELAN_HOME=os.environ.get('ELAN_HOME', '/opt/elan'),
               HEAVY_MEM_GB='1.5', HEAVY_SLOTS='1', HEAVY_MAX_LOAD='off',
               SENTINEL='space λ $literal')
    for key in ('HEAVY_BUDGET_DIR', 'LEAN_SYSROOT', 'LAKE_OVERRIDE_LEAN',
                'HEAVY_OBSERVE_DIR', 'HEAVY_LOG', 'FREN_BUILD_REQUESTS_FILE',
                'FREN_BUILD_ALLOWANCE_KIB', 'FREN_BUILD_HEADROOM_KIB',
                'FREN_BUILD_FALLBACK_KIB', 'FREN_BUILD_TIMEOUT_MS'):
        env.pop(key, None)
    (work / 'lean-toolchain').write_text(pin + '\n')
    nested = work / 'caller'; nested.mkdir()
    def states():
        return set(work.glob('fren-build-*'))
    def invoke(label, command, *, extra=None, script=HEAVY, cancel=False):
        before = states()
        local = dict(env, **(extra or {}))
        ready = work / (label + '.pid'); local['READY'] = str(ready)
        argv = [str(script), '--offline', *map(str, command)]
        probe = OwnedRun(heavy, work, label)
        # Legacy fixtures publish a plain PID; only the wrapper is signalled.
        if cancel:
            cancel_ready = work / (label + '.cancel-ready')
            def action(owner, process, data):
                owner.send(process.pid, signal.SIGTERM)
            # Adapt the old readiness file without trusting its numeric PID.
            original_collect = probe.collect
            def collect():
                found = original_collect()
                if ready.exists() and not cancel_ready.exists():
                    cancel_ready.write_text('{}')
                return found
            probe.collect = collect
        row, out, err = probe.execute(argv, cwd=nested, env=local,
            ready=cancel_ready if cancel else None, action=action if cancel else None)
        code = row['physical_status']
        new = sorted(states() - before)
        row['states'] = list(map(str, new))
        log = work / 'home/.cache/heavy/log.jsonl'
        if log.exists():
            row['heavy'] = json.loads(log.read_text().splitlines()[-1])
        results.append(row)
        (work / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        if row['failure'] or row['cleanup']['outcome'] != 'complete':
            raise AssertionError(row)
        return code, out, err, new
    # Baseline negative: old Heavy does not dispatch to the controller.
    baseline = work / 'old-heavy'
    baseline.write_bytes(subprocess.check_output(['git', 'show',
        'f7f319d0b1748cee8e521f6c032749edffc446c2:scripts/heavy'], cwd=ROOT))
    baseline.chmod(0o755)
    code, _, _, new = invoke('old-no-dispatch', [lake, 'build'],
                             extra={'CONTROL': 'assert-gated'}, script=baseline)
    assert code == 19 and not new
    code, _, _, new = invoke('new-dispatch', [lake, 'build'], extra={'CONTROL': 'assert-gated'})
    assert code == 0 and len(new) == 1
    code, out, err, new = invoke('literal-streams', [lake, '--no-cache', 'build', 'a b', '$x', 'λ'],
                                 extra={'STATUS': '7', 'CONTROL': 'pipes'})
    assert code == 7 and out.endswith(b'O' * 131072) and err.endswith(b'E' * 131072)
    data = json.loads(out.splitlines()[0])
    assert data['argv'] == ['--no-cache', 'build', 'a b', '$x', 'λ']
    assert data['cwd'] == str(nested) and data['sentinel'] == env['SENTINEL']
    assert data['stdin'] == 'input λ\n' and data['budget'] and data['sysroot']
    assert data['net'] != os.readlink('/proc/self/ns/net')
    assert new[0].stat().st_mode & 0o777 == 0o700
    assert (new[0] / 'requests.tsv').read_text() == ''
    # Dispatch must not select the script checkout's Lake or caller directory.
    code, out, _, _ = invoke('directory-operand', [lake, '-d', str(work), 'build', 'x'])
    assert code == 0 and json.loads(out)['argv'] == ['-d', str(work), 'build', 'x']
    code, _, _, _ = invoke('signal', [lake, 'build'], extra={'CONTROL': 'signal'})
    assert code == 143
    code, out, err, _ = invoke('missing-direct', [lake, 'env'], extra={'CONTROL': 'missing'})
    direct = (code, out, err)
    code, out, err, new = invoke('missing-gated', [lake, 'build'], extra={'CONTROL': 'missing'})
    assert code == direct[0] != 0 and out == direct[1]
    assert err.split(b'\n', 1)[1] == direct[2], (err, direct)
    rows = [json.loads(p.read_text()) for p in (new[0] / 'state/overlay/records').glob('process-*.json')]
    assert any(r['child_present'] and r['raw_wait_status'] != 0 and r['gate_errno'] == 0
               and r['request_provenance'] == 'explicit-unknown-fallback' for r in rows)
    for label, extra in (
        ('excess-allowance', {'FREN_BUILD_ALLOWANCE_KIB': '99999999'}),
        ('small-outer', {'HEAVY_MEM_GB': '.05'}),
        ('bad-headroom', {'FREN_BUILD_HEADROOM_KIB': '99999999'}),
        ('bad-fallback', {'FREN_BUILD_FALLBACK_KIB': '0'}),
        ('missing-requests', {'FREN_BUILD_REQUESTS_FILE': str(work / 'absent')}),
        ('already-budgeted', {'HEAVY_BUDGET_DIR': str(work / 'unowned')}),
        ('existing-overlay', {'LEAN_SYSROOT': str(work / 'unowned')})):
        code, _, _, _ = invoke(label, [lake, 'build'], extra=extra)
        assert code == 125, (label, code)
    manifest = work / 'requests'; manifest.write_text('bad\n')
    code, _, _, _ = invoke('malformed-requests', [lake, 'build'],
                           extra={'FREN_BUILD_REQUESTS_FILE': str(manifest)})
    assert code == 125
    # Explicit native Lake stays explicit even with an unrelated elan override.
    code, _, _, _ = invoke('explicit-lake', [lake, 'build'], extra={'ELAN_TOOLCHAIN': 'uninstalled-test-pin'})
    assert code == 0
    for label, prefix, extra in (
        ('missing-toolchain', ['lake'], {'ELAN_TOOLCHAIN': 'uninstalled-test-pin'}),
        ('plus-toolchain', ['lake', '+uninstalled-test-pin'], {})):
        code, _, err, new = invoke(label, [*prefix, 'build'], extra=extra)
        assert code == 125 and b'not installed' in err and not new
        assert b'download' not in err and b'could not check' not in err
    # Real elan shim discovery uses the parent caller pin, not -d's pin.
    selected_env = dict(env)
    selected_env.pop('ELAN_TOOLCHAIN', None)
    with mock.patch.dict(os.environ, selected_env, clear=True):
        old_cwd = Path.cwd()
        os.chdir(nested)
        try:
            selected, command = build.selected_lake(['lake', '+' + pin, 'build'], selected_env)
        finally:
            os.chdir(old_cwd)
    assert selected.resolve() == real and command == [str(real.parent / 'lake'), 'build']
    with mock.patch.dict(os.environ, env, clear=True):
        selected, command = build.selected_lake(['lake', '+v4.32.0', 'build'], dict(env))
    assert selected.resolve() == real and command == [str(real.parent / 'lake'), 'build']
    # Normal non-build and bootstrap argv retain their original invocation.
    for label, command in (('non-build', [lake, 'env', 'literal build']),
                           ('option-operand', [lake, '-K', 'build', 'env']),
                           ('bootstrap', [lake, '-d', str(ROOT / 'tools/heavy-observe'), 'build', 'budget_session'])):
        code, out, _, new = invoke(label, command)
        assert code == 0 and not new and json.loads(out)['budget'] is None
    missing = work / 'missing/scripts'; missing.mkdir(parents=True)
    for name in ('heavy', 'fren-build', 'heavy-lean-build'):
        dest = missing / name; dest.write_bytes((ROOT / 'scripts' / name).read_bytes()); dest.chmod(0o755)
    code, _, err, new = invoke('missing-tools', [lake, 'build'], script=missing / 'heavy')
    assert code == 125 and b'missing prebuilt' in err and not new
    # Actual recursive overlay rejection, before any compiler can exec itself.
    recursive = work / 'recursive'; recursive.mkdir()
    recursive_lake = recursive / 'lake'
    recursive_lake.write_bytes(lake.read_bytes()); recursive_lake.chmod(0o755)
    (recursive / 'lean').symlink_to(ROOT / 'tools/heavy-observe/.lake/build/bin/heavy_observe')
    code, _, err, _ = invoke('recursive-compiler', [recursive_lake, 'build'])
    assert code == 125 and b'recursive overlay' in err
    (recursive / 'lean').unlink()
    code, _, err, new = invoke('missing-compiler', [recursive_lake, 'build'])
    assert code == 125 and b'missing compiler' in err and not new
    code, _, _, _ = invoke('cancellation', [lake, 'build'], extra={'CONTROL': 'wait'}, cancel=True)
    assert code == 125  # The controller retains wait status 15 and reports cancellation.
    assert b'cleanup errno=0; command wait status=15' in (work / 'cancellation.stderr').read_bytes()
    code, _, err, _ = invoke('outer-backstop', [lake, 'build'], extra={
        'CONTROL': 'memory', 'HEAVY_MEM_GB': '.2', 'FREN_BUILD_HEADROOM_KIB': '1000',
        'FREN_BUILD_FALLBACK_KIB': '1000'})
    assert code == 137 and b'heavy: killed' in err
    row = results[-1]['heavy']
    assert row['compiler_budget'] and row['peak_rss_kb'] > int(.2 * 1024 * 1024)
    code, _, err, new = invoke('already-budgeted-explicit', [ROOT / 'scripts/heavy-lean-build',
        '--state', str(work / 'must-not-exist'), '--real-lean', real,
        '--allowance-kib', '1300000', '--headroom-kib', '100000',
        '--fallback-kib', '600000', '--timeout-ms', '30000',
        '--requests', manifest, '--', lake, 'build'],
        extra={'HEAVY_BUDGET_DIR': str(work / 'unowned')})
    assert code == 125 and b'already budgeted' in err and not new
    assert not (work / 'must-not-exist').exists()
    # Registry leases must all have been released, including failed/cancelled calls.
    assert heavy.jobs(str(work / 'home/.cache/heavy')) == []
    summary = {'cases': len(results), 'status': 'passed', 'real_lean': str(real),
               'compiler_sha256': hashlib.sha256(real.read_bytes()).hexdigest(),
               'results': str(work / 'results.json')}
    (work / 'report.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
