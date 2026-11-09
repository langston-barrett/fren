#!/usr/bin/env python3
"""Optional setup and owned harness regressions; no real Lean target workloads."""
import json
import os
from pathlib import Path
import select
import signal
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
from owned_test import run as owned_run
from orphan_test import controls as orphan_controls, status_controls


def workspace(mode):
    parent = Path(os.environ.get('HEAVY_AUTOMATIC_TEST_ROOT', HERE / 'test-work'))
    existed = parent.exists()
    if os.environ.get('HEAVY_AUTOMATIC_REQUIRE_FRESH') == '1':
        assert not existed, parent
    parent.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix='automatic-' + mode + '-', dir=parent))
    (work / 'setup.json').write_text(json.dumps(dict(mode=mode, parent=str(parent),
        parent_preexisting=existed, created_parent=True)))
    return work


def io_controls(work):
    prefix = work / 'fixture'; (prefix / 'bin').mkdir(parents=True)
    compiler = prefix / 'bin/lean'
    compiler.write_text('#!' + sys.executable + '\n' + r'''
import json,os,pathlib,sys
args=sys.argv[1:]
if args==['--print-prefix']: print(pathlib.Path(__file__).resolve().parent.parent)
elif args==['--version']: print('fixture Lean')
elif args==['--githash']: print('f'*40)
else:
 pathlib.Path(os.environ['COMPILER_MARKER']).write_text('actual fixture exec')
 leases=[p.read_text().split() for p in pathlib.Path(os.environ['HEAVY_BUDGET_DIR']).glob('ticket-*')]
 pathlib.Path(os.environ['LIVE_MARKER']).write_text(json.dumps(leases))
 if '-o' in args: pathlib.Path(args[args.index('-o')+1]).write_bytes(b'fixture artifact')
 print('fixture stdout',flush=True); print('fixture stderr',file=sys.stderr,flush=True)
 sys.exit(int(os.environ.get('FIXTURE_STATUS','0')))
''')
    compiler.chmod(0o755)
    pkg = work / 'pkg'; pkg.mkdir(); (pkg / 'Input.lean').write_text('fixture input\n')
    home = work / 'home'; home.mkdir()
    manifest = work / 'requests'; manifest.write_text('')
    driver = work / 'driver.py'
    # The command remains group leader; the observer is its same-group child,
    # exactly as in Lake. The enclosing owned runner/controller owns teardown.
    driver.write_text("import os,pathlib,subprocess,sys\npathlib.Path(os.environ['COMMAND_MARKER']).write_text('command launched')\np=os.environ['LEAN_SYSROOT']+'/bin/lean'\nsys.exit(subprocess.call([p,'Input.lean','-o','out']))\n")
    worker = work / 'fault.py'
    worker.write_text(r'''
import builtins,errno,json,pathlib,runpy,sys
config=json.loads(pathlib.Path(sys.argv[1]).read_text())
fault=config['fault']
write_text=pathlib.Path.write_text; write_bytes=pathlib.Path.write_bytes; unlink=pathlib.Path.unlink
hits=[]
def hit(kind,path):
 hits.append([kind,str(path)])
 write_text(pathlib.Path(config['hits']),json.dumps(hits))
def text(self,*args,**kwargs):
 if self.name=='real-lean.path' and fault=='mandatory':
  hit('mandatory',self);raise OSError(errno.ENOSPC,'required metadata failure')
 if self.name=='compiler-padding' and fault in ('padding','padding-cleanup'):
  hit('padding',self)
  if fault=='padding-cleanup': write_text(self,*args,**kwargs)
  raise OSError(errno.ENOSPC,'optional padding failure')
 return write_text(self,*args,**kwargs)
def data(self,*args,**kwargs):
 if self.name=='compiler-history.json' and fault in ('history','history-cleanup'):
  hit('history',self);write_bytes(self,*args,**kwargs)
  if fault=='history-cleanup': write_text(self.with_name('compiler-padding'),'123')
  raise OSError(errno.ENOSPC,'optional snapshot failure')
 return write_bytes(self,*args,**kwargs)
def remove(self,*args,**kwargs):
 if fault in ('padding-cleanup','history-cleanup') and self.name in ('compiler-history.json','compiler-padding'):
  hit('cleanup',self);raise OSError(errno.EACCES,'optional cleanup failure')
 return unlink(self,*args,**kwargs)
pathlib.Path.write_text=text;pathlib.Path.write_bytes=data;pathlib.Path.unlink=remove
original_import=builtins.__import__
def imported(name,*args,**kwargs):
 if name=='history' and fault=='import':
  hit('import',pathlib.Path('history'));raise ImportError('optional helper unavailable')
 return original_import(name,*args,**kwargs)
builtins.__import__=imported
sys.argv=config['argv'];runpy.run_path(sys.argv[0],run_name='__main__')
''')
    env = dict(os.environ, HOME=str(home), HEAVY_COMPILER_CPU_SECONDS='10', HEAVY_COMPILER_WALL_MS='5000',
               FREN_BUILD_PADDING_KIB='123')
    for key in ('HEAVY_BUDGET_DIR','LEAN_SYSROOT','LAKE_OVERRIDE_LEAN','HEAVY_AUTOMATIC_PADDING_KIB'):
        env.pop(key, None)
    results = []
    def case(label, fault='', *, request=manifest, status=0, expect=None, launched=True):
        state = work / label
        command_marker = work / (label + '.command'); marker = work / (label + '.compiler')
        live = work / (label + '.live.json')
        config = work / (label + '.config.json'); hits = work / (label + '.hits.json')
        argv = [str(ROOT / 'scripts/heavy-lean-build'), '--state', str(state), '--real-lean', str(compiler),
                '--allowance-kib','1300000','--headroom-kib','100000','--fallback-kib','600000',
                '--timeout-ms','1000','--requests',str(request),'--',sys.executable,str(driver)]
        config.write_text(json.dumps(dict(fault=fault,argv=argv,hits=str(hits))))
        p = owned_run([sys.executable,'-I',str(worker),str(config)],directory=work,label=label,cwd=pkg,
                      env=dict(env,COMMAND_MARKER=str(command_marker),COMPILER_MARKER=str(marker),LIVE_MARKER=str(live),FIXTURE_STATUS=str(status)),timeout=5)
        rows = [json.loads(f.read_bytes()) for f in (state / 'overlay/records').glob('process-*.json')]
        record = next((r for r in rows if r.get('schema')==3),None)
        item = dict(case=label,fault=fault,status=p.returncode,stdout=p.stdout.decode(),stderr=p.stderr.decode(),
                    command_launched=command_marker.exists(),compiler_launched=marker.exists(),session_created=(state/'session').exists(),
                    record=record,live_lease=json.loads(live.read_text()) if live.exists() else [],hits=json.loads(hits.read_text()) if hits.exists() else [],
                    qualifier='Scripted compiler fixture through actual observer/session; no real Lean target measurement.')
        results.append(item);(work/'result.json').write_text(json.dumps(results,indent=2))
        assert p.returncode == (status if expect is None else expect), item
        assert marker.exists()==launched,item
        if launched:
            assert command_marker.exists() and record['child_present'] and record['gate_errno']==0,item
            assert record['raw_wait_status']==status*256 and record['shell_code']==status,item
            assert len(item['live_lease'])==1 and item['live_lease'][0][1]=='1',item
            assert int(item['live_lease'][0][2])==record['requested_reservation_kib'],item
            assert p.stdout==b'fixture stdout\n' and p.stderr==b'fixture stderr\n',item
            assert not (state/'session/owner').stat().st_size==0
        return record
    a=case('sample-one');b=case('sample-two');known=case('known-advice')
    assert a['request_provenance']==b['request_provenance']=='explicit-unknown-fallback'
    assert known['request_provenance']=='automatic-cohort-estimate' and known['automatic_sample_count']==2
    for fault in ('import','padding','history','padding-cleanup','history-cleanup'):
        r=case(fault,fault,status=7)
        assert r['requested_reservation_kib']==600000 and r['request_provenance']=='explicit-unknown-fallback'
        if fault.endswith('-cleanup'):
            assert r['automatic_sample_count']==2
            assert (work/fault/'overlay/compiler-history.json').exists()
            assert (work/fault/'overlay/compiler-padding').read_text()=='123'
    explicit=work/'explicit';explicit.write_text(f"{pkg/'Input.lean'}\t{a['source_before']}\t444444\n")
    r=case('explicit-precedence','padding-cleanup',request=explicit,status=7)
    assert r['requested_reservation_kib']==444444 and r['request_provenance']=='explicit-source-request'
    bad=work/'bad';bad.write_text('malformed\n')
    case('invalid-explicit','padding',request=bad,expect=125,launched=False)
    assert not results[-1]['command_launched']
    case('mandatory-failure','mandatory',expect=125,launched=False)
    assert not results[-1]['session_created'] and not results[-1]['command_launched']
    huge=work/'huge';huge.write_text(f"{pkg/'Input.lean'}\t{a['source_before']}\t2000000\n")
    r=case('oversized-explicit',request=huge,expect=125,launched=False)
    assert r['gate_errno']!=0 and not r['child_present'] and r['requested_reservation_kib']==2000000
    print(f'automatic optional IO controls passed: {work}')


def ownership_controls(work):
    home=work/'home';home.mkdir()
    env=dict(os.environ,HOME=str(home),HEAVY_MEM_GB='1.5',HEAVY_SLOTS='1',HEAVY_MAX_LOAD='off')
    for key in ('HEAVY_LOG','HEAVY_BUDGET_DIR','LEAN_SYSROOT','LAKE_OVERRIDE_LEAN'):
        env.pop(key,None)
    helper=work/'sleeper.py'
    helper.write_text(r'''
import json,os,pathlib,signal,sys,time
ready,term=map(pathlib.Path,sys.argv[1:3]);finish=None
ignore=len(sys.argv)>3
# Publish readiness only after the cancellation handler owns cleanup.
def cancel(sig,frame):
 global finish
 term.write_text('owned TERM received')
 if finish is None and not ignore: finish=time.monotonic()+.25
signal.signal(signal.SIGTERM,cancel)
ready.write_text(json.dumps({'pid':os.getpid(),'sid':os.getsid(0)}))
while finish is None or time.monotonic()<finish: time.sleep(.01)
''')
    heavy=ROOT/'scripts/heavy'
    ready=work/'timeout.ready';term=work/'timeout.term';pinned=[]
    def pin(owner, process, data):
        owner.collect()
        assert data['sid']==data['pid'] and data['pid']!=process.pid, data
        assert any(key[0]==data['pid'] for key in owner.handles),data
        pinned.append(os.pidfd_open(data['pid']))
    try:
        try:
            owned_run([str(heavy),'--offline',sys.executable,str(helper),str(ready),str(term)],
                      directory=work,label='timeout',env=env,timeout=.2,ready=ready,action=pin)
        except subprocess.TimeoutExpired: pass
        else: raise AssertionError('timeout did not cancel the owned Heavy monitor')
        receipt=json.loads((work/'timeout.json').read_text())
        assert receipt['cleanup']['outcome']=='complete' and receipt['physical_status_known'],receipt
        for fd in pinned:
            poll=select.poll();poll.register(fd,select.POLLIN);assert poll.poll(0),'owned child survived timeout'
    finally:
        for fd in pinned:os.close(fd)
    ready_kill=work/'escalation.ready';term_kill=work/'escalation.term';pinned=[]
    try:
        try:
            owned_run([str(heavy),'--offline',sys.executable,str(helper),str(ready_kill),str(term_kill),'ignore'],
                      directory=work,label='escalation',env=env,timeout=.2,grace=.2,
                      ready=ready_kill,action=pin)
        except subprocess.TimeoutExpired: pass
        else: raise AssertionError('escalation did not time out')
        escalated=json.loads((work/'escalation.json').read_text())
        assert term_kill.exists() and escalated['cleanup']['outcome']=='complete',escalated
        assert escalated['cleanup']['seconds']>=.2,escalated
        for fd in pinned:
            poll=select.poll();poll.register(fd,select.POLLIN);assert poll.poll(0),'owned child survived escalation'
    finally:
        for fd in pinned:os.close(fd)
    # A nested harness is the same adapter boundary used by test.py dispatch.
    # Repeat cancellation after the real command has entered TERM cleanup.
    nested=work/'nested.py'
    nested.write_text("import sys\nfrom pathlib import Path\nsys.path.insert(0,"+repr(str(HERE))+")\nfrom owned_test import run\nrun(sys.argv[3:],directory=Path(sys.argv[1]),label='inner',timeout=5,ready=Path(sys.argv[2]))\n")
    ready=work/'repeat.ready';term=work/'repeat.term'
    def cancel_twice(owner, process, data):
        owner.send(process.pid,signal.SIGTERM)
        deadline=time.monotonic()+2
        while not term.exists() and time.monotonic()<deadline:
            owner.collect();time.sleep(.01)
        assert term.exists(),'owned command never entered cleanup'
        owner.send(process.pid,signal.SIGTERM)
    p=owned_run([sys.executable,'-I',str(nested),str(work),str(ready),str(heavy),'--offline',
                 sys.executable,str(helper),str(ready),str(term)],directory=work,label='repeat',env=env,
                timeout=5,grace=5,ready=ready,action=cancel_twice)
    inner=json.loads((work/'inner.json').read_text());outer=json.loads((work/'repeat.json').read_text())
    assert p.returncode==143 and inner['cancel_signals']==[15,15],inner
    assert inner['cleanup']['outcome']==outer['cleanup']['outcome']=='complete'
    assert not inner['cleanup']['remaining'] and not outer['cleanup']['remaining']
    orphans = orphan_controls(work, env)
    statuses = status_controls(work, env)
    (work/'result.json').write_text(json.dumps(dict(timeout=receipt,escalation=escalated,inner=inner,outer=outer,orphans=orphans,statuses=statuses),indent=2))
    print(f'automatic owned cancellation controls passed: {work}')


if __name__=='__main__':
    mode=sys.argv[1];assert mode in ('io','ownership')
    work=workspace(mode)
    (io_controls if mode=='io' else ownership_controls)(work)
