"""Prepare memory subgroups inside an existing dedicated, finite job scope.

No sibling scope, service or cap change. Only verified members of this launch
chain may move within their original aggregate. Unsupported setups remain
unavailable; the selected compiler's native gate must then refuse exec.
"""
import json
import os
from pathlib import Path
import secrets
import subprocess

CG = Path('/sys/fs/cgroup')


def location():
    lines = Path('/proc/self/cgroup').read_text().splitlines()
    line, = [s for s in lines if s.startswith('0::')]
    relative = line[3:]
    if not relative.startswith('/') or '..' in Path(relative).parts:
        raise ValueError('invalid native cgroup path')
    return CG / relative.lstrip('/')


def identity(pid):
    text = Path(f'/proc/{pid}/stat').read_text()
    fields = text[text.rfind(')') + 2:].split()
    return int(fields[1]), int(fields[19])


def prepare():
    current = location()
    # A subsequent entry in the same owned build may reuse its prepared tree.
    if current.name.startswith('heavy-driver-'):
        token = current.name.removeprefix('heavy-driver-')
        modules = current.parent / ('heavy-modules-' + token)
        if not modules.is_dir() or modules.stat().st_uid != os.geteuid():
            raise ValueError('unowned prepared module root')
        if 'memory' not in (modules / 'cgroup.subtree_control').read_text().split():
            raise ValueError('prepared memory controller unavailable')
        return dict(aggregate=str(current.parent), driver=str(current), modules=str(modules),
                    reused=True, moved=[])
    # Never restructure an interactive/service/other agent's shared cgroup.
    if not current.name.endswith('.scope') or not current.name.startswith(('fren-job-', 'heavy-')):
        raise ValueError('module memory needs a dedicated transient job scope')
    maximum = (current / 'memory.max').read_text().strip()
    if not maximum.isdecimal() or int(maximum) <= 0:
        raise ValueError('aggregate scope must have a finite positive memory.max')
    if 'memory' not in (current / 'cgroup.controllers').read_text().split():
        raise ValueError('memory controller not available from aggregate ancestor')
    ancestors = {}
    pid = os.getpid()
    while pid > 1:
        parent, start = identity(pid);ancestors[pid] = start;pid = parent
    members = set(map(int, (current / 'cgroup.procs').read_text().split()))
    if not members or os.getpid() not in members or not members <= ancestors.keys():
        raise ValueError('foreign/non-launch-chain aggregate member; no migration performed')
    def policy():
        p = subprocess.run(['systemctl', '--user', 'show', current.name,
                            '-p', 'ControlGroup', '-p', 'Transient', '-p', 'Delegate', '-p', 'OOMPolicy'],
                           capture_output=True, text=True, timeout=3, check=True)
        return dict(line.split('=', 1) for line in p.stdout.splitlines() if '=' in line)
    before_policy = policy()
    if before_policy.get('Transient') != 'yes' or before_policy.get('ControlGroup') != '/' + str(current.relative_to(CG)):
        raise ValueError('scope manager identity is not this owned transient aggregate')
    # A nested OOM must not trigger systemd's aggregate stop policy. These
    # properties must be supplied when the owned scope is created; this host
    # does not permit setting them on an already-active scope.
    if before_policy.get('Delegate') != 'yes' or before_policy.get('OOMPolicy') != 'continue':
        raise ValueError('scope must start with Delegate=yes and OOMPolicy=continue')
    after_policy = before_policy
    handles = {}
    driver = modules = None
    moved = []
    try:
        for pid in members:
            fd = os.pidfd_open(pid);handles[pid] = fd
            if identity(pid)[1] != ancestors[pid]:
                raise ValueError('launch-chain identity changed')
        token = secrets.token_hex(16)
        driver = current / ('heavy-driver-' + token)
        # Actual kernel permissions/delegation decide support. Do not modify
        # systemd units, ownership, other scopes or aggregate cap settings.
        driver.mkdir(mode=0o700)
        if set(map(int, (current / 'cgroup.procs').read_text().split())) != members:
            raise ValueError('aggregate membership changed before migration')
        for pid, fd in handles.items():
            pinned = next(int(s.split()[1]) for s in Path(f'/proc/self/fdinfo/{fd}').read_text().splitlines() if s.startswith('Pid:'))
            if pinned != pid or identity(pid)[1] != ancestors[pid]:
                raise ValueError('launch-chain ownership lost')
            (driver / 'cgroup.procs').write_text(str(pid))
            moved.append(dict(pid=pid, start=ancestors[pid]))
        if (current / 'cgroup.procs').read_text().strip():
            raise ValueError('unexpected aggregate members after owned migration')
        (current / 'cgroup.subtree_control').write_text('+memory')
        modules = current / ('heavy-modules-' + token);modules.mkdir(mode=0o700)
        (modules / 'cgroup.subtree_control').write_text('+memory')
        if (current / 'memory.max').read_text().strip() != maximum:
            raise ValueError('aggregate cap changed')
        return dict(aggregate=str(current), driver=str(driver), modules=str(modules),
                    reused=False, moved=moved, aggregate_memory_max=maximum, policy_before=before_policy, policy_after=after_policy,
                    subtree=(current / 'cgroup.subtree_control').read_text().strip())
    finally:
        for fd in handles.values():os.close(fd)
        # Live launch-chain members retain the driver until the scope retires.
        if driver is not None and not moved:
            try:driver.rmdir()
            except OSError:pass


def configure(env, output, source_root):
    env.pop('HEAVY_MODULE_MEMORY_ROOT', None)
    env['HEAVY_MODULE_SOURCE_ROOT'] = str(Path(source_root).resolve())
    try:
        result = prepare()
        pool = Path(result['modules'])
        build = pool / ('build-' + str(os.getpid()) + '-' + secrets.token_hex(16))
        build.mkdir(mode=0o700)
        (build / 'cgroup.subtree_control').write_text('+memory')
        result['module_pool'] = str(pool)
        result['modules'] = str(build)
        env['HEAVY_MODULE_MEMORY_ROOT'] = str(build)
        result['status'] = 'available'
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        result = dict(status='unavailable', error=repr(error))
    try:
        Path(output).write_text(json.dumps(result, indent=2) + '\n')
    except OSError:
        pass  # Diagnostics cannot replace the command's physical status.
    return result
