#!/usr/bin/env python3
"""Actual selected-module scope/readback/physical controls; no numerical model."""
import json
from concurrent.futures import ThreadPoolExecutor
import hashlib
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
from owned_test import run


def fixture(work):
    prefix=work/'compiler';(prefix/'bin').mkdir(parents=True)
    compiler=prefix/'bin/lean'
    compiler.write_text('#!'+sys.executable+'\n'+r'''
import json,os,pathlib,signal,sys,time
args=sys.argv[1:]
if args==['--print-prefix']: print(pathlib.Path(__file__).resolve().parent.parent);sys.exit(0)
if args==['--version']: print('memory fixture');sys.exit(0)
if args==['--githash']: print('f'*40);sys.exit(0)
relative=next(s[3:] for s in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if s.startswith('0::'))
cg=pathlib.Path('/sys/fs/cgroup')/relative.lstrip('/')
mode=os.environ['MODE'];marker=pathlib.Path(os.environ['MARKER'])
info=dict(args=args,cwd=os.getcwd(),pid=os.getpid(),parent=os.getppid(),scope=str(cg),inode=cg.stat().st_ino,maximum=(cg/'memory.max').read_text().strip(),swap=(cg/'memory.swap.max').read_text().strip())
marker.write_text(json.dumps(info))
print('fixture stdout',flush=True);print('fixture stderr',file=sys.stderr,flush=True)
if mode=='term':os.kill(os.getpid(),signal.SIGTERM)
if mode in ('oom','cancel','leftover'):
 child=os.fork()
 if child==0:
  os.setsid()
  if mode!='oom': signal.signal(signal.SIGTERM,signal.SIG_IGN)
  child_info=dict(pid=os.getpid(),session=os.getsid(0),scope=relative)
  if mode=='oom':pathlib.Path(str(marker)+'.child').write_text(json.dumps(child_info))
  data=bytearray((96 if mode=='oom' else 16)*1024*1024)
  for i in range(0,len(data),4096): data[i]=1
  if mode!='oom':pathlib.Path(str(marker)+'.child').write_text(json.dumps(child_info))
  time.sleep(10);os._exit(0)
 info['child']=child;marker.write_text(json.dumps(info))
 if mode=='leftover':
  deadline=time.monotonic()+2
  while not pathlib.Path(str(marker)+'.child').exists() and time.monotonic()<deadline:time.sleep(.005)
  assert pathlib.Path(str(marker)+'.child').exists()
  if '-o' in args and os.environ.get('NO_ARTIFACT')!='1':pathlib.Path(args[args.index('-o')+1]).write_bytes(b'fixture artifact')
  sys.exit(0)
 if mode=='cancel':
  signal.signal(signal.SIGTERM,signal.SIG_IGN)
  deadline=time.monotonic()+2
  while not pathlib.Path(str(marker)+'.child').exists() and time.monotonic()<deadline:time.sleep(.005)
  pathlib.Path(str(marker)+'.ready').write_text(json.dumps(info))
 os.waitpid(child,0)
else:
 data=bytearray(16*1024*1024)
 for i in range(0,len(data),4096):data[i]=1
 if '-o' in args and os.environ.get('NO_ARTIFACT')!='1':pathlib.Path(args[args.index('-o')+1]).write_bytes(b'fixture artifact')
 sys.exit(7 if mode=='exit7' else 0)
''')
    compiler.chmod(0o755)
    driver=work/'driver.py'
    driver.write_text("import json,os,subprocess,sys\np=subprocess.run([os.environ['LEAN_SYSROOT']+'/bin/lean',*json.loads(os.environ.get('EXTRA_ARGS','[]')),sys.argv[1],'-o',sys.argv[2]])\nsys.exit(p.returncode if p.returncode>=0 else 128-p.returncode)\n")
    home=work/'home';home.mkdir();manifest=work/'requests';manifest.write_text('')
    return compiler,driver,home,manifest


def controls(work, part):
    compiler,driver,home,manifest=fixture(work)
    selected=ROOT/'src/FrenBase/Identity.lean';legacy=ROOT/'src/FrenTestMain.lean'
    env=dict(os.environ,HOME=str(home),HEAVY_MEM_GB='6',HEAVY_MAX_LOAD='off')
    for k in ('HEAVY_BUDGET_DIR','LEAN_SYSROOT','LAKE_OVERRIDE_LEAN','HEAVY_LOG','HEAVY_COMPILER_CPU_SECONDS','HEAVY_COMPILER_WALL_MS','FREN_BUILD_REQUESTS_FILE'):env.pop(k,None)
    results=[]
    def case(label,mode='below',source=selected,cap='67108864',extra=None,cancel=False,unknown=False,cleanup_cancel=0):
        state=work/label;marker=work/(label+'.marker');local=dict(env,MODE=mode,MARKER=str(marker),HEAVY_COMPILER_MEMORY_BYTES=cap)
        local.update(extra or {})
        ready=Path(str(marker)+'.ready') if cancel else None
        cleanup_entries=[]
        signals_sent=[]
        if cleanup_cancel:
            entries=work/(label+'-cleanup');entries.mkdir()
            ready=entries/'first.json'
            local.update(MODULE_FAULT='cleanup-entry',MODULE_CLEANUP_DIR=str(entries))
        command=[str(ROOT/'scripts/heavy-lean-build'),'--state',str(state),'--real-lean',str(compiler),
                 '--allowance-kib','1300000','--headroom-kib','100000','--fallback-kib','600000','--timeout-ms','2000','--requests',str(manifest),
                 '--',sys.executable,str(driver),str(source),str(work/(label+'.out'))]
        def action(owner,process,data):
            if not cleanup_cancel:
                owner.send(process.pid,signal.SIGTERM)
                signals_sent.append(dict(pid=process.pid,signal=signal.SIGTERM));return
            # Native IO interposition pauses the observer immediately before
            # its actual cgroup.kill. The compiler leader has already exited.
            info=json.loads(marker.read_text())
            assert data['pid']==info['parent'] and data['path']==info['scope']+'/cgroup.kill',data
            assert 'populated 1' in (Path(info['scope'])/'cgroup.events').read_text()
            child=json.loads(Path(str(marker)+'.child').read_text())
            members=list(map(int,(Path(info['scope'])/'cgroup.procs').read_text().split()))
            assert child['pid'] in members and info['pid'] not in members,(info,child,members)
            assert os.getsid(child['pid'])==child['pid'],child
            data['kernel_members_before_kill']=members
            cleanup_entries.append(data)
            owner.send(process.pid,signal.SIGTERM)
            signals_sent.append(dict(pid=process.pid,signal=signal.SIGTERM))
            session_entry=entries/(str(process.pid)+'.json')
            deadline=time.monotonic()+2
            while not session_entry.exists() and time.monotonic()<deadline:
                owner.collect();time.sleep(.005)
            assert session_entry.exists(),'session did not enter owned module cleanup'
            observed=json.loads(session_entry.read_text())
            assert observed['pid']==process.pid and observed['path']==data['path'],observed
            cleanup_entries.append(observed)
            for _ in range(cleanup_cancel-1):
                owner.send(process.pid,signal.SIGTERM)
                signals_sent.append(dict(pid=process.pid,signal=signal.SIGTERM));time.sleep(.01)
            (entries/'release').write_text('release owned cleanup')
        p=run(command,directory=work,label=label,env=local,timeout=5,grace=3,
              ready=ready,action=action if cancel or cleanup_cancel else None)
        rows=[json.loads(f.read_text()) for f in (state/'overlay/records').glob('process-*.json')]
        record=next((r for r in rows if r.get('schema')==3),None)
        setup=json.loads((state/'module-memory-setup.json').read_text())
        session=json.loads((state/'session/module-memory-result.json').read_text())
        item=dict(case=label,status=p.returncode,stdout=p.stdout.decode(),stderr=p.stderr.decode(),record=record,setup=setup,session=session,
                  marker=json.loads(marker.read_text()) if marker.exists() else None,
                  child=json.loads(Path(str(marker)+'.child').read_text()) if Path(str(marker)+'.child').exists() else None,
                  cleanup_entries=cleanup_entries,
                  cancellation_signals=signals_sent,
                  compiler_physical_status=(record['raw_wait_status'] if record is not None
                      and record['child_present'] and record['wait_errno']==0 else 'unknown'))
        results.append(item);(work/'results.json').write_text(json.dumps(results,indent=2)+'\n')
        if record and record['compiler_memory_applied_bytes']:
            assert record['compiler_memory_ack_pid']==record['child_pid']==item['marker']['pid'],item
            assert record['compiler_memory_expected_inode']==record['compiler_memory_observed_inode']==item['marker']['inode'],item
            assert int(item['marker']['maximum'])==record['compiler_memory_readback_bytes']==int(cap),item
            assert item['marker']['scope']==record['compiler_memory_scope'],item
            assert item['marker']['scope'].startswith(setup['aggregate']+'/heavy-modules-'),item
            assert record['compiler_memory_effective_bytes']<=int(cap),item
            assert record['compiler_memory_swap_readback_bytes']==0,item
            if not unknown:
                assert record['compiler_memory_cleanup_errno']==0 and record['compiler_memory_populated_after']==0,item
        if not unknown:
            assert session['module_memory_cleanup_errno']==0,item
            assert not Path(setup.get('modules','/not-created')).exists(),item
        return item
    if part in ('producer','lifecycle'):
        # Establish the private layout before introducing the foreign sibling.
        a=case('below');assert a['status']==0 and a['record']['compiler_memory_applied_bytes']==67108864,a
        assert a['stdout']=='fixture stdout\n' and a['stderr']=='fixture stderr\n',a
    if part=='producer':
        b=case('oom','oom');assert b['status']==137 and b['record']['raw_wait_status']==9,b
        assert b['record']['compiler_memory_oom_kill_delta']>=1 and b['record']['compiler_memory_oom_delta']>=1,b
        assert b['child'] and b['child']['scope']==b['marker']['scope'].removeprefix('/sys/fs/cgroup'),b
    if part in ('producer','lifecycle'):
        library=faults(work)
        # Foreign fixture is a sibling of the observers, never in a module leaf.
        foreign=subprocess.Popen([sys.executable,'-I','-c','import time;time.sleep(10)'])
        fd=os.pidfd_open(foreign.pid)
        before=Path(f'/proc/{foreign.pid}/cgroup').read_text()
        try:
            c=case('cancel','cancel',cancel=True);assert c['status'] in (125,143),c
            assert foreign.poll() is None and Path(f'/proc/{foreign.pid}/cgroup').read_text()==before
            assert c['child'] and not Path(c['setup']['modules']).exists(),c
            c=case('successful-leftover','leftover')
            assert c['status']==0 and c['record']['raw_wait_status']==0,c
            assert c['stdout']=='fixture stdout\n' and c['stderr']=='fixture stderr\n',c
            assert c['child']['session']==c['child']['pid'],c
            assert c['record']['compiler_memory_oom_kill_delta']==0,c
            for count in (1,3):
                c=case('cleanup-cancel-'+str(count),'leftover',
                       extra=dict(LD_PRELOAD=str(library)),cleanup_cancel=count)
                assert c['status'] in (125,143),c
                assert len(c['cleanup_entries'])==2 and c['child']['session']==c['child']['pid'],c
                assert len(c['cancellation_signals'])==count,c
                # Cancellation after observer handler restoration can prevent
                # publication. Session wait is not a compiler wait substitute.
                if c['record'] is not None:assert c['record']['raw_wait_status']==0,c
                else:assert c['compiler_physical_status']=='unknown',c
                assert c['stdout']=='fixture stdout\n',c
            assert foreign.poll() is None and Path(f'/proc/{foreign.pid}/cgroup').read_text()==before
        finally:
            signal.pidfd_send_signal(fd,signal.SIGTERM);foreign.wait(timeout=2);os.close(fd)
    if part=='negative':
        # First preparation must refuse a foreign member without moving it.
        foreign=subprocess.Popen([sys.executable,'-I','-c','import time;time.sleep(10)'])
        fd=os.pidfd_open(foreign.pid);before=Path(f'/proc/{foreign.pid}/cgroup').read_text()
        try:
            a=case('foreign-preparation');assert a['status']==125 and a['marker'] is None,a
            assert a['setup']['status']=='unavailable' and 'foreign' in a['setup']['error'],a
            assert foreign.poll() is None and Path(f'/proc/{foreign.pid}/cgroup').read_text()==before
        finally:
            signal.pidfd_send_signal(fd,signal.SIGTERM);foreign.wait(timeout=2);os.close(fd)
        a=case('invalid',cap='0');assert a['status']==125 and a['marker'] is None,a
        assert a['record']['compiler_memory_applied_bytes'] is None,a
        for setting in ('-1','abc','1125899906842625',''):
            a=case('invalid-'+str(len(results)),cap=setting)
            assert a['status']==125 and a['marker'] is None and a['record']['child_pid']==0,a
        b=case('legacy','exit7',source=legacy);assert b['status']==7 and not b['record']['compiler_memory_selected'],b
        assert b['stdout']=='fixture stdout\n' and b['stderr']=='fixture stderr\n',b
        b=case('legacy-invalid-setting','exit7',source=legacy,cap='0')
        assert b['status']==7 and not b['record']['compiler_memory_selected'],b
        a=case('ambiguous',extra=dict(EXTRA_ARGS='["--unsupported"]'))
        assert a['status']==125 and a['marker'] is None and a['record']['input_kind']=='unknown',a
        library=faults(work)
        for fault in ('write','readback','cleanup'):
            a=case('fault-'+fault,extra=dict(LD_PRELOAD=str(library),MODULE_FAULT=fault),unknown=fault=='cleanup')
            assert a['status']==125,a
            if fault=='cleanup':
                assert a['marker'] and a['record']['raw_wait_status']==0,a
                assert a['record']['compiler_memory_applied_bytes']==67108864,a
                assert a['record']['compiler_memory_cleanup_errno'] and a['session']['module_memory_cleanup_errno'],a
                # Fault injection leaves empty, exclusively owned directories.
                build=Path(a['setup']['modules'])
                for leaf in build.iterdir():
                    if leaf.name.startswith('m-'):
                        assert 'populated 0' in (leaf/'cgroup.events').read_text()
                        leaf.rmdir()
                build.rmdir()
            else:
                assert a['marker'] is None and a['record']['compiler_memory_applied_bytes'] is None,a
                assert a['record']['compiler_memory_setup_errno'],a
    print(json.dumps(dict(work=str(work),part=part,cases=len(results))))
    return results


def faults(work):
    """Inject actual native IO faults, never a supplied selection verdict."""
    source=work/'memory-fault.c'
    source.write_text(r'''#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>
static int target(int fd,const char *file) {
 char link[64],path[4096];snprintf(link,sizeof(link),"/proc/self/fd/%d",fd);
 ssize_t n=readlink(link,path,sizeof(path)-1);if(n<0)return 0;path[n]=0;
 return strstr(path,"/heavy-modules-")&&strstr(path,"/m-")&&strstr(path,file);
}
int mkdir(const char *path,mode_t mode) {
 const char *fault=getenv("MODULE_FAULT");
 if(fault&&!strcmp(fault,"prepare")&&strstr(path,"/heavy-modules-")&&strstr(path,"/build-")) {
  errno=EACCES;return -1;
 }
 return syscall(SYS_mkdir,path,mode);
}
ssize_t write(int fd,const void *p,size_t n) {
 const char *mode=getenv("MODULE_FAULT");
 static int held=0;
 if(!held&&mode&&!strcmp(mode,"cleanup-entry")&&target(fd,"/cgroup.kill")) {
  held=1;char path[4096],link[64],message[4300],file[4096],temporary[4096],release[4096];
  snprintf(link,sizeof(link),"/proc/self/fd/%d",fd);ssize_t k=readlink(link,path,sizeof(path)-1);
  if(k<0)return -1;
  path[k]=0;
  const char *dir=getenv("MODULE_CLEANUP_DIR");if(!dir){errno=EINVAL;return -1;}
  int size=snprintf(message,sizeof(message),"{\"pid\":%ld,\"path\":\"%s\"}",(long)getpid(),path);
  snprintf(temporary,sizeof(temporary),"%s/%ld.tmp",dir,(long)getpid());
  int mark=syscall(SYS_openat,AT_FDCWD,temporary,O_WRONLY|O_CREAT|O_EXCL,0600);
  if(mark<0)return -1;
  syscall(SYS_write,mark,message,size);close(mark);
  snprintf(file,sizeof(file),"%s/%ld.json",dir,(long)getpid());
  if(rename(temporary,file)<0)return -1;
  snprintf(temporary,sizeof(temporary),"%s/first.json",dir);
  syscall(SYS_linkat,AT_FDCWD,file,AT_FDCWD,temporary,0);
  snprintf(release,sizeof(release),"%s/release",dir);
  struct timespec begin,now,pause={0,5000000};clock_gettime(CLOCK_MONOTONIC,&begin);
  do {
   if(access(release,F_OK)==0)break;
   nanosleep(&pause,NULL);clock_gettime(CLOCK_MONOTONIC,&now);
  } while((now.tv_sec-begin.tv_sec)*1000000000LL+now.tv_nsec-begin.tv_nsec<1500000000LL);
 }
 if(mode&&!strcmp(mode,"write")&&target(fd,"/memory.max")){errno=ENOSPC;return -1;}
 return syscall(SYS_write,fd,p,n);
}
ssize_t pread(int fd,void *p,size_t n,off_t offset) {
 ssize_t k=syscall(SYS_pread64,fd,p,n,offset);const char *mode=getenv("MODULE_FAULT");
 if(k>0&&mode&&!strcmp(mode,"readback")&&target(fd,"/memory.max")) {
  const char *bad="67108865\n";size_t size=strlen(bad);if(n>=size){memcpy(p,bad,size);return size;}
 }
 return k;
}
int unlinkat(int dir,const char *name,int flags) {
 const char *mode=getenv("MODULE_FAULT");
 if(mode&&!strcmp(mode,"cleanup")&&!strncmp(name,"m-",2)){errno=EBUSY;return -1;}
 return syscall(SYS_unlinkat,dir,name,flags);
}
''')
    library=work/'memory-fault.so'
    run(['cc','-shared','-fPIC','-Wall','-Wextra','-Werror',str(source),'-o',str(library)],
        directory=work,label='fault-build',timeout=5,check=True)
    return library


def direct_controls(work):
    """Ordinary Heavy/Lake env dispatch with actual session/kernel readbacks."""
    from owned_test import _build
    _build.direct_routes(work)
    start=time.monotonic()
    compiler,_,home,_=fixture(work)
    lake=compiler.parent/'lake'
    lake.write_text('#!'+sys.executable+'\n'+r'''
import os,pathlib,subprocess,sys
args=sys.argv[1:];tail=args[args.index('env')+1:]
exe=str(pathlib.Path(__file__).parent/'lean') if tail[0]=='lean' else tail[0]
p=subprocess.run([exe,*tail[1:]])
sys.exit(p.returncode if p.returncode>=0 else 128-p.returncode)
''')
    lake.chmod(0o755)
    env=dict(os.environ,HOME=str(home),TMPDIR=str(work),HEAVY_MEM_GB='6',HEAVY_MAX_LOAD='off')
    for k in ('HEAVY_BUDGET_DIR','LEAN_SYSROOT','LAKE_OVERRIDE_LEAN','HEAVY_LOG',
              'HEAVY_COMPILER_CPU_SECONDS','HEAVY_COMPILER_WALL_MS','HEAVY_COMPILER_MEMORY_BYTES',
              'FREN_BUILD_REQUESTS_FILE','FREN_BUILD_ALLOWANCE_KIB','FREN_BUILD_HEADROOM_KIB',
              'FREN_BUILD_FALLBACK_KIB','FREN_BUILD_TIMEOUT_MS'):
        env.pop(k,None)
    results=[]
    def case(label,args,mode='below',executable=lake,script=ROOT/'scripts/heavy',extra=None,cwd=ROOT):
        marker=work/(label+'.marker')
        command=[str(script),'--offline',str(executable),'env','lean',*map(str,args)]
        p=run(command,directory=work,label=label,cwd=cwd,
              env=dict(env,MODE=mode,MARKER=str(marker),NO_ARTIFACT='1',**(extra or {})),timeout=8,grace=3)
        match=re.search(rb'fren-build: retained private state: ([^\n]+)',p.stderr)
        state=Path(os.fsdecode(match[1]))/'state' if match else None
        rows=[json.loads(f.read_text()) for f in (state/'overlay/records').glob('process-*.json')] if state else []
        row=dict(case=label,command=command,status=p.returncode,stdout=p.stdout.decode(),stderr=p.stderr.decode(),
                 marker=json.loads(marker.read_text()) if marker.exists() else None,records=rows,state=str(state))
        if state:
            row['setup']=json.loads((state/'module-memory-setup.json').read_text())
            row['session']=json.loads((state/'session/module-memory-result.json').read_text())
        results.append(row);(work/'direct-results.json').write_text(json.dumps(results,indent=2)+'\n')
        return row
    selected=ROOT/'src/FrenBase/Identity.lean'
    # Real mkdir denial at the mandatory per-build delegation boundary, also
    # when this job has already prepared its aggregate for another partition.
    library=faults(work)
    r=case('direct-unavailable',[selected],extra={'LD_PRELOAD':str(library),'MODULE_FAULT':'prepare'})
    assert r['status']==125 and r['marker'] is None,r
    assert r['setup']['status']=='unavailable' and 'PermissionError' in r['setup']['error'],r
    assert r['records'][0]['child_present'] is False,r
    # direct_routes checks exact unchanged argv for every excluded mode using
    # the actual native classifier and wrapper adapter. One legacy process
    # witnesses the unchanged end-to-end path; avoid repeating that transport.
    r=case('direct-legacy',[ROOT/'src/FrenTestMain.lean'])
    assert r['status']==0 and not r['records'] and r['state']=='None',r
    args=['-o','--run','src/FrenBase/Identity.lean']
    r=case('direct-selected',args,'exit7')
    assert r['status']==7 and r['stdout']=='fixture stdout\n',r
    assert r['stderr'].endswith('fixture stderr\n') and r['marker']['cwd']==str(ROOT),r
    assert r['marker']['args']==list(map(str,args)),r
    record=r['records'][0];marker=r['marker']
    assert record['raw_wait_status']==7*256 and record['real_compiler']==str(compiler),r
    assert record['compiler_memory_ack_pid']==record['child_pid']==marker['pid'],r
    assert record['compiler_memory_expected_inode']==record['compiler_memory_observed_inode']==marker['inode'],r
    assert record['compiler_memory_applied_bytes']==record['compiler_memory_readback_bytes']==1073741824,r
    assert record['compiler_memory_effective_bytes']==1073741824 and marker['swap']=='0',r
    assert record['compiler_memory_cleanup_errno']==0 and record['compiler_memory_populated_after']==0,r
    assert r['session']['module_memory_cleanup_errno']==0 and not Path(r['setup']['modules']).exists(),r
    new_root=ROOT/'src/Fren2CheckMain.lean'
    r=case('direct-new-root',[new_root],mode='exit7')
    assert r['status']==7 and len(r['records'])==1,r
    record=r['records'][0];marker=r['marker']
    assert record['args']==[str(new_root)] and record['compiler_memory_source']==str(new_root),r
    assert record['compiler_memory_selected'] and record['raw_wait_status']==7*256,r
    assert record['compiler_memory_applied_bytes']==record['compiler_memory_readback_bytes']==1073741824,r
    assert record['compiler_memory_swap_readback_bytes']==0 and marker['swap']=='0',r
    assert record['compiler_memory_ack_pid']==record['child_pid']==marker['pid'],r
    assert record['compiler_memory_expected_inode']==record['compiler_memory_observed_inode']==marker['inode'],r
    assert record['compiler_memory_cleanup_errno']==0 and record['compiler_memory_populated_after']==0,r
    assert r['session']['module_memory_cleanup_errno']==0 and not Path(r['setup']['modules']).exists(),r
    for label,args in [('new-root-query',['--version',new_root]),
                       ('new-root-run',['--run',new_root]), ('new-root-stdin',['--stdin',new_root])]:
        r=case(label,args)
        assert r['status']==0 and not r['records'] and r['state']=='None',r
    r=case('direct-signal',[selected],mode='term')
    assert r['status']==143 and r['records'][0]['raw_wait_status']==15,r
    assert r['records'][0]['compiler_memory_cleanup_errno']==0 and not Path(r['setup']['modules']).exists(),r
    missing=work/'missing/scripts';missing.mkdir(parents=True)
    for name in ('heavy','fren-build','heavy-lean-build'):
        p=missing/name;p.write_bytes((ROOT/'scripts'/name).read_bytes());p.chmod(0o755)
    r=case('direct-missing-tools',[selected],script=missing/'heavy')
    assert r['status']==125 and r['marker'] is None and not r['records'],r
    # The real compiler controls need no project dependencies or Lake update.
    (work/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage directControl\n')
    (work/'lean-toolchain').write_bytes((ROOT/'lean-toolchain').read_bytes())
    real=Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip())/'bin/lean'
    alias=work/'source-alias';alias.symlink_to(selected)
    alternate=work/'source-alias.txt';alternate.symlink_to(selected)
    for path in (alias,alternate):
        # -j1 is valid Lean syntax outside the conservative metadata subset.
        # Both the standalone verdict and the observer must see through aliases.
        verdict=run([str(HERE/'.lake/build/bin/heavy_observe'),'--classify-direct',str(ROOT/'src'),'-j1',str(path)],
                    directory=work,label='classify-'+path.name,env=env,timeout=3)
        assert verdict.returncode==0 and verdict.stdout==b'selected\n',verdict
    native=run([str(real),'-j1',str(alias)],directory=work,label='native-alias-threads',env=env,timeout=5)
    assert native.returncode==0 and native.stdout==native.stderr==b'',native
    r=case('direct-ambiguous',['-j1',alias],executable=real.parent/'lake',cwd=work)
    records=[v for v in r['records'] if v.get('compiler_memory_selected')]
    assert r['status']==125 and len(records)==1 and not records[0]['child_present'],r
    assert records[0]['compiler_memory_source']==str(selected) and records[0]['input_kind']=='unknown',r
    assert r['session']['module_memory_cleanup_errno']==0 and not Path(r['setup']['modules']).exists(),r
    artifact=work/'Identity λ $literal.olean'
    r=case('direct-actual-lean',['--root',ROOT,alias,'-o',artifact],executable=real.parent/'lake',cwd=work)
    records=[v for v in r['records'] if v.get('compiler_memory_selected')]
    assert r['status']==0 and artifact.is_file() and len(records)==1,r
    record=records[0]
    assert record['args']==['--root',str(ROOT),str(alias),'-o',str(artifact)] and record['cwd']==str(work),r
    assert record['compiler_memory_source']==str(selected),r
    assert record['compiler_memory_applied_bytes']==record['compiler_memory_effective_bytes']==1073741824,r
    assert record['compiler_memory_ack_pid']==record['child_pid'] and record['compiler_memory_expected_inode']==record['compiler_memory_observed_inode'],r
    assert record['raw_wait_status']==0 and record['compiler_memory_cleanup_errno']==0 and record['compiler_memory_populated_after']==0,r
    assert not Path(record['compiler_memory_scope']).exists() and not Path(r['setup']['modules']).exists(),r
    (work/'direct-summary.json').write_text(json.dumps(dict(status='passed',cases=len(results),
        control_wall_seconds=time.monotonic()-start,results=str(work/'direct-results.json')),indent=2)+'\n')
    print(f'direct Lean controls passed: {work}')


def direct_run_controls(work):
    """Program execution bypasses compiler admission in both native spellings."""
    from owned_test import _build
    build=_build.load(ROOT/'scripts/fren-build')
    real=Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip())/'bin/lean'
    selected=ROOT/'src/FrenBase/Identity.lean'
    home=work/'home';home.mkdir()
    env=dict(os.environ,HOME=str(home),HEAVY_MEM_GB='6',HEAVY_MAX_LOAD='off')
    for key in ('HEAVY_BUDGET_DIR','LEAN_SYSROOT','LAKE_OVERRIDE_LEAN','HEAVY_LOG'):
        env.pop(key,None)
    start=time.monotonic();results=[]
    for flag in ('-r','--run'):
        native_command=[str(real.parent/'lake'),'env','lean',flag,str(selected)]
        assert build.heavy_command(native_command,1300000)==native_command
        native=run(native_command,directory=work,label='native-'+flag.lstrip('-'),cwd=ROOT,env=env,timeout=5)
        wrapped_command=[str(ROOT/'scripts/heavy'),'--offline',*native_command]
        wrapped=run(wrapped_command,directory=work,label='heavy-'+flag.lstrip('-'),cwd=ROOT,env=env,timeout=5)
        row=dict(flag=flag,native_command=native_command,wrapped_command=wrapped_command,
                 native_status=native.returncode,status=wrapped.returncode,
                 native_stdout=native.stdout.decode(),stdout=wrapped.stdout.decode(),
                 native_stderr=native.stderr.decode(),stderr=wrapped.stderr.decode())
        results.append(row);(work/'run-results.json').write_text(json.dumps(results,indent=2)+'\n')
        assert native.returncode==wrapped.returncode==1,row
        assert native.stdout==wrapped.stdout and native.stderr==wrapped.stderr,row
        assert b"unknown declaration 'main'" in wrapped.stderr,row
    (work/'run-summary.json').write_text(json.dumps(dict(status='passed',control_wall_seconds=time.monotonic()-start,
        cgroup=Path('/proc/self/cgroup').read_text(),results=str(work/'run-results.json')),indent=2)+'\n')
    print(f'direct Lean run controls passed: {work}')


def direct_option_controls(work, shard, operand=False):
    """Apparent mode flags can instead be filenames or option operands."""
    real=Path(subprocess.check_output(['lean','--print-prefix'],text=True).strip())/'bin/lean'
    selected=ROOT/'src/FrenBase/Identity.lean'
    home=work/'home';home.mkdir()
    env=dict(os.environ,HOME=str(home),TMPDIR=str(work),HEAVY_MEM_GB='6',HEAVY_MAX_LOAD='off',HEAVY_SLOTS='2')
    for key in ('HEAVY_BUDGET_DIR','LEAN_SYSROOT','LAKE_OVERRIDE_LEAN','HEAVY_LOG'):
        env.pop(key,None)
    prefix='operand' if operand else 'terminator'
    if operand:
        cases=[('long-save',['--incr-save','--version',str(selected)],'--version'),
               ('long-header',['--incr-header-save','--run',str(selected)],'--run'),
               ('long-error',['--error','--run',str(selected)],None),
               ('short-save',['-Y','--version',str(selected)],'--version'),
               ('short-header',['-H','--run',str(selected)],'--run'),
               ('short-error',['-E','--run',str(selected)],None)][3*shard:3*shard+3]
    else:
        flags=('--run','-r','--stdin','--version','-v','--short-version','-V',
               '--githash','-g','--help','-h','--features','--print-prefix','--print-libdir')
        cases=[(flag,['--',flag],None) for flag in flags[shard::2]]
    start=time.monotonic();results=[]
    if not operand:
        for flag,_,_ in cases:(work/flag).symlink_to(selected)
    def case(item):
        flag,args,snapshot_name=item
        cwd=work/flag if operand else work
        if operand:cwd.mkdir()
        native_command=[str(real.parent/'lake'),'-d',str(ROOT),'--offline','env','lean',*args]
        # The existing owned dispatch owns this helper and all descendants.
        # Each subprocess waits for its exact child; an exception
        # leaves the outer dispatch responsible for bounded family cleanup.
        native=subprocess.run(native_command,cwd=cwd,env=env,capture_output=True,timeout=5)
        snapshot=cwd/snapshot_name if snapshot_name else None
        snapshot_bytes=snapshot.read_bytes() if snapshot and snapshot.exists() else None
        wrapped_command=[str(ROOT/'scripts/heavy'),'--offline',*native_command]
        wrapped=subprocess.run(wrapped_command,cwd=cwd,env=env,capture_output=True,timeout=5)
        match=re.search(rb'fren-build: retained private state: ([^\n]+)',wrapped.stderr)
        state=Path(os.fsdecode(match[1]))/'state' if match else None
        records=[json.loads(p.read_text()) for p in (state/'overlay/records').glob('process-*.json')] if state else []
        row=dict(flag=flag,args=args,native_command=native_command,wrapped_command=wrapped_command,cwd=str(cwd),
                 native_status=native.returncode,status=wrapped.returncode,
                 native_stdout=native.stdout.decode(),native_stderr=native.stderr.decode(),
                 stdout=wrapped.stdout.decode(),stderr=wrapped.stderr.decode(),records=records)
        if snapshot_name:
            row['snapshot']=dict(path=str(snapshot),bytes=len(snapshot_bytes) if snapshot_bytes is not None else 0,
                sha256=hashlib.sha256(snapshot_bytes).hexdigest() if snapshot_bytes is not None else None)
        if state:
            row['setup']=json.loads((state/'module-memory-setup.json').read_text())
            row['session']=json.loads((state/'session/module-memory-result.json').read_text())
        (work/(prefix+'-'+flag+'.json')).write_text(json.dumps(row,indent=2)+'\n')
        assert native.returncode==0 and native.stdout==native.stderr==b'',row
        if snapshot_name:assert snapshot_bytes and snapshot.read_bytes()==snapshot_bytes,row
        selected_records=[r for r in records if r.get('compiler_memory_selected')]
        assert wrapped.returncode==125 and len(selected_records)==1,row
        r=selected_records[0]
        assert r['args']==args and r['compiler_memory_source']==str(selected),row
        assert r['input_kind']=='unknown' and not r['child_present'] and r['compiler_memory_applied_bytes'] is None,row
        assert row['setup']['status']=='available' and row['session']['module_memory_cleanup_errno']==0,row
        assert not Path(row['setup']['modules']).exists(),row
        return row
    # Prepare the owned hierarchy before concurrent callers exist. Each later
    # caller has a private build root; ordinary Heavy admission still applies.
    results.append(case(cases[0]))
    with ThreadPoolExecutor(max_workers=2) as pool:
        for row in pool.map(case,cases[1:]):
            results.append(row)
            (work/(prefix+'-results.json')).write_text(json.dumps(results,indent=2)+'\n')
    logs=[json.loads(line) for line in (home/'.cache/heavy/log.jsonl').read_text().splitlines()]
    assert len(logs)==len(cases) and all(r['compiler_budget'] and r['exit_status']==125 for r in logs),logs
    (work/(prefix+'-summary.json')).write_text(json.dumps(dict(status='passed',shard=shard,cases=len(results),
        control_wall_seconds=time.monotonic()-start,cgroup=Path('/proc/self/cgroup').read_text(),
        results=str(work/(prefix+'-results.json'))),indent=2)+'\n')
    print(f'direct Lean {prefix} controls passed: {work}')


def actual_compile(work):
    """One existing small Fren2 module; only owned outputs/cache are cold."""
    package=work/'real-package';package.mkdir()
    (package/'lean-toolchain').write_bytes((ROOT/'lean-toolchain').read_bytes())
    (package/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage memoryExample\n'
        f'lean_lib FrenBase where\n  srcDir := "{ROOT}/src"\n  roots := #[`FrenBase.Identity]\n')
    env=dict(os.environ,HOME=str(work/'real-home'),LAKE_CACHE_DIR=str(work/'real-cache'),HEAVY_MEM_GB='6',HEAVY_MAX_LOAD='off')
    Path(env['HOME']).mkdir()
    for key in ('HEAVY_BUDGET_DIR','LEAN_SYSROOT','LAKE_OVERRIDE_LEAN','HEAVY_COMPILER_MEMORY_BYTES','FREN_BUILD_REQUESTS_FILE'):
        env.pop(key,None)
    command=[str(ROOT/'scripts/heavy'),'lake','-d',str(package),'build','+FrenBase.Identity:olean','--offline','--no-cache','--wfail']
    start=time.monotonic()
    result=run(command,directory=work,label='actual-compile',env=env,timeout=12,grace=3)
    match=re.search(rb'fren-build: retained private state: ([^\n]+)',result.stderr)
    state=Path(os.fsdecode(match[1]))/'state' if match else None
    records=[json.loads(p.read_text()) for p in (state/'overlay/records').glob('process-*.json')] if state else []
    selected=[r for r in records if r.get('compiler_memory_selected')]
    row=dict(command=command,status=result.returncode,stdout=result.stdout.decode(),stderr=result.stderr.decode(),
             elapsed_seconds=time.monotonic()-start,state=str(state),records=records,
             artifact=str(package/'.lake/build/lib/lean/FrenBase/Identity.olean'))
    (work/'actual-compile-result.json').write_text(json.dumps(row,indent=2)+'\n')
    assert result.returncode==0 and len(selected)==1,row
    r=selected[0]
    assert r['compiler_memory_applied_bytes']==1073741824 and r['compiler_memory_ack_pid']==r['child_pid'],row
    assert r['raw_wait_status']==0 and r['compiler_memory_cleanup_errno']==0 and r['compiler_memory_populated_after']==0,row
    assert Path(row['artifact']).is_file(),row


if __name__=='__main__':
    part=sys.argv[1];assert part in ('producer','negative','lifecycle','direct','directRun',
        'directTerminator0','directTerminator1','directOperands0','directOperands1')
    parent=Path(os.environ.get('HEAVY_MODULE_TEST_ROOT',HERE/'test-work'));parent.mkdir(parents=True,exist_ok=True)
    work=Path(tempfile.mkdtemp(prefix='module-'+part+'-',dir=parent))
    if part=='direct':direct_controls(work)
    elif part=='directRun':direct_run_controls(work)
    elif part.startswith('directTerminator'):direct_option_controls(work,int(part[-1]))
    elif part.startswith('directOperands'):direct_option_controls(work,int(part[-1]),operand=True)
    else:controls(work,part)
    if part=='producer':actual_compile(work)
