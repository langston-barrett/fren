#!/usr/bin/env python3
"""Actual selected-module scope/readback/physical controls; no numerical model."""
import json
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
info=dict(pid=os.getpid(),scope=str(cg),inode=cg.stat().st_ino,maximum=(cg/'memory.max').read_text().strip(),swap=(cg/'memory.swap.max').read_text().strip())
marker.write_text(json.dumps(info))
print('fixture stdout',flush=True);print('fixture stderr',file=sys.stderr,flush=True)
if mode in ('oom','cancel'):
 child=os.fork()
 if child==0:
  os.setsid()
  pathlib.Path(str(marker)+'.child').write_text(json.dumps(dict(pid=os.getpid(),scope=relative)))
  if mode=='cancel': signal.signal(signal.SIGTERM,signal.SIG_IGN)
  data=bytearray((96 if mode=='oom' else 16)*1024*1024)
  for i in range(0,len(data),4096): data[i]=1
  time.sleep(10);os._exit(0)
 info['child']=child;marker.write_text(json.dumps(info))
 if mode=='cancel':
  signal.signal(signal.SIGTERM,signal.SIG_IGN)
  deadline=time.monotonic()+2
  while not pathlib.Path(str(marker)+'.child').exists() and time.monotonic()<deadline:time.sleep(.005)
  pathlib.Path(str(marker)+'.ready').write_text(json.dumps(info))
 os.waitpid(child,0)
else:
 data=bytearray(16*1024*1024)
 for i in range(0,len(data),4096):data[i]=1
 if '-o' in args:pathlib.Path(args[args.index('-o')+1]).write_bytes(b'fixture artifact')
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
    def case(label,mode='below',source=selected,cap='67108864',extra=None,cancel=False,unknown=False):
        state=work/label;marker=work/(label+'.marker');local=dict(env,MODE=mode,MARKER=str(marker),HEAVY_COMPILER_MEMORY_BYTES=cap)
        local.update(extra or {})
        command=[str(ROOT/'scripts/heavy-lean-build'),'--state',str(state),'--real-lean',str(compiler),
                 '--allowance-kib','1300000','--headroom-kib','100000','--fallback-kib','600000','--timeout-ms','2000','--requests',str(manifest),
                 '--',sys.executable,str(driver),str(source),str(work/(label+'.out'))]
        def action(owner,process,data):owner.send(process.pid,signal.SIGTERM)
        p=run(command,directory=work,label=label,env=local,timeout=5,grace=3,
              ready=Path(str(marker)+'.ready') if cancel else None,action=action if cancel else None)
        rows=[json.loads(f.read_text()) for f in (state/'overlay/records').glob('process-*.json')]
        record=next((r for r in rows if r.get('schema')==3),None)
        setup=json.loads((state/'module-memory-setup.json').read_text())
        session=json.loads((state/'session/module-memory-result.json').read_text())
        item=dict(case=label,status=p.returncode,stdout=p.stdout.decode(),stderr=p.stderr.decode(),record=record,setup=setup,session=session,
                  marker=json.loads(marker.read_text()) if marker.exists() else None,
                  child=json.loads(Path(str(marker)+'.child').read_text()) if Path(str(marker)+'.child').exists() else None)
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
    if part=='producer':
        a=case('below');assert a['status']==0 and a['record']['compiler_memory_applied_bytes']==67108864,a
        assert a['stdout']=='fixture stdout\n' and a['stderr']=='fixture stderr\n',a
        b=case('oom','oom');assert b['status']==137 and b['record']['raw_wait_status']==9,b
        assert b['record']['compiler_memory_oom_kill_delta']>=1 and b['record']['compiler_memory_oom_delta']>=1,b
        assert b['child'] and b['child']['scope']==b['marker']['scope'].removeprefix('/sys/fs/cgroup'),b
        # Foreign fixture is a sibling of the observers, never in a module leaf.
        foreign=subprocess.Popen([sys.executable,'-I','-c','import time;time.sleep(10)'])
        fd=os.pidfd_open(foreign.pid)
        before=Path(f'/proc/{foreign.pid}/cgroup').read_text()
        try:
            c=case('cancel','cancel',cancel=True);assert c['status'] in (125,143),c
            assert foreign.poll() is None and Path(f'/proc/{foreign.pid}/cgroup').read_text()==before
            assert c['child'] and not Path(c['setup']['modules']).exists(),c
        finally:
            signal.pidfd_send_signal(fd,signal.SIGTERM);foreign.wait(timeout=2);os.close(fd)
    else:
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
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <unistd.h>
static int target(int fd,const char *file) {
 char link[64],path[4096];snprintf(link,sizeof(link),"/proc/self/fd/%d",fd);
 ssize_t n=readlink(link,path,sizeof(path)-1);if(n<0)return 0;path[n]=0;
 return strstr(path,"/heavy-modules-")&&strstr(path,"/m-")&&strstr(path,file);
}
ssize_t write(int fd,const void *p,size_t n) {
 const char *mode=getenv("MODULE_FAULT");
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
    part=sys.argv[1];assert part in ('producer','negative')
    parent=Path(os.environ.get('HEAVY_MODULE_TEST_ROOT',HERE/'test-work'));parent.mkdir(parents=True,exist_ok=True)
    work=Path(tempfile.mkdtemp(prefix='module-'+part+'-',dir=parent));controls(work,part)
    if part=='producer':actual_compile(work)
