#!/usr/bin/env python3
"""Bounded, optional storage of raw successful compiler observations."""
import fcntl
import hashlib
import json
import os
import re
import secrets
import stat
import sys
import time

AGE = 7 * 86400 * 10**9
LIMIT = 16 * 1024 * 1024
MAX_RECORD = 65536
FIELDS = ('source', 'cwd', 'source_before', 'real_compiler', 'compiler_fingerprint',
          'compiler_version', 'compiler_githash', 'args', 'setup', 'setup_fingerprint', 'boot_id')
NAME = re.compile(r'^[0-9a-f]{64}\.json$')


def decode(raw):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result: raise ValueError('duplicate JSON field')
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=unique,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('invalid number')))


def cohort(r, boot, now):
    """Check raw status and the conservative supported argv grammar."""
    try:
        if type(r['schema']) is not int or r['schema'] != 3 or r['family'] != 'lean' or r['input_kind'] != 'file': return None
        if any(type(r[k]) is not int or r[k] != 0 for k in
               ('launch_errno', 'exec_errno', 'wait_errno', 'clock_errno', 'raw_wait_status', 'gate_errno', 'wrapper_code')): return None
        if r['child_present'] is not True: return None
        if any(type(r[k]) is not int for k in ('child_pid', 'start_monotonic_ns', 'end_monotonic_ns', 'peak_rss_kib', 'measured_peak_rss_kib')): return None
        if not (r['child_pid'] > 0 and 0 <= r['start_monotonic_ns'] <= r['end_monotonic_ns'] <= now and
                now - r['end_monotonic_ns'] <= AGE and r['peak_rss_kib'] > 0 and r['peak_rss_kib'] == r['measured_peak_rss_kib']): return None
        if not boot or r['boot_id'] != boot or r['source_after'] != r['source_before']: return None
        for k in FIELDS[:7]:
            if not isinstance(r[k], str) or not r[k]: return None
        if not r['cwd'].startswith('/') or not r['real_compiler'].startswith('/'): return None
        if (r['setup'] is None) != (r['setup_fingerprint'] is None): return None
        if r['setup'] is not None and (not isinstance(r['setup'], str) or not r['setup'] or not isinstance(r['setup_fingerprint'], str) or not r['setup_fingerprint']): return None
        args = r['args']
        if not isinstance(args, list) or not all(isinstance(x, str) for x in args): return None
        operands = {'-o', '-i', '-c', '-b', '--setup', '-R', '--root'}
        flags = {'--json', '-q', '--stats', '-Dweak.fren.runChecks=false'}
        source = setup = None
        i = 0
        while i < len(args):
            a = args[i]; i += 1
            if a in operands:
                if i == len(args): return None
                if a == '--setup': setup = args[i]
                i += 1
            elif a in flags: pass
            elif a.startswith('-') or source is not None: return None
            else: source = a
        if source != r['source'] or setup != r['setup']: return None
        key = json.dumps([r[k] for k in FIELDS], ensure_ascii=True, separators=(',', ':'))
        if len(key.encode()) > 65536: return None
        return key
    except (KeyError, TypeError, ValueError):
        return None


def directory(parent, name, create=False, private=False):
    if create:
        try: os.mkdir(name, 0o700, dir_fd=parent)
        except FileExistsError: pass
    fd = os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC, dir_fd=parent)
    st = os.fstat(fd)
    if create and (st.st_uid != os.geteuid() or (private and stat.S_IMODE(st.st_mode) != 0o700)):
        os.close(fd); raise ValueError('unowned or non-private directory')
    return fd


def publish(raw, home):
    if len(raw) > MAX_RECORD: raise ValueError('record too large')
    with open('/proc/sys/kernel/random/boot_id', encoding='ascii') as f:
        boot = f.read().strip()
    now = time.monotonic_ns()
    record = decode(raw)
    key = cohort(record, boot, now)
    if key is None: return False
    # Walk with no symlinks and hold directory descriptors throughout the update.
    fd = os.open('/', os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        for part in os.path.abspath(home).split('/')[1:]:
            nxt = directory(fd, part); os.close(fd); fd = nxt
        for part in ('.cache', 'heavy'):
            nxt = directory(fd, part, create=True); os.close(fd); fd = nxt
        parent = os.dup(fd)
        nxt = directory(fd, 'compiler-observations', create=True, private=True)
        os.close(fd); fd = nxt
        def check_directory():
            named = os.stat('compiler-observations', dir_fd=parent, follow_symlinks=False)
            actual = os.fstat(fd)
            if not stat.S_ISDIR(named.st_mode) or (named.st_dev, named.st_ino) != (actual.st_dev, actual.st_ino):
                raise ValueError('spool directory replaced')
        lock = os.open('.lock', os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600, dir_fd=fd)
        try:
            st = os.fstat(lock)
            if not stat.S_ISREG(st.st_mode) or st.st_uid != os.geteuid() or st.st_nlink != 1: raise ValueError('invalid lock')
            deadline = time.monotonic() + 1.0
            while True:
                try:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    if time.monotonic() >= deadline: raise TimeoutError('spool lock busy')
                    time.sleep(0.005)
            check_directory()
            rows = []
            for name in os.listdir(fd):
                if name == '.lock': continue
                if not NAME.fullmatch(name): raise ValueError('unexpected spool entry')
                f = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC, dir_fd=fd)
                try:
                    st = os.fstat(f)
                    if not stat.S_ISREG(st.st_mode) or st.st_uid != os.geteuid() or st.st_nlink != 1 or stat.S_IMODE(st.st_mode) != 0o600 or st.st_size > MAX_RECORD: raise ValueError('invalid spool file')
                    data = os.read(f, MAX_RECORD + 1)
                    if len(data) != st.st_size or hashlib.sha256(data).hexdigest() + '.json' != name: raise ValueError('changed spool file')
                finally: os.close(f)
                try:
                    obj = decode(data); k = cohort(obj, boot, now)
                except (ValueError, UnicodeError): k = None
                rows.append((name, data, k, obj['end_monotonic_ns'] if k else -1))
            existing = {row[0] for row in rows}
            data = raw if isinstance(raw, bytes) else raw.encode()
            name = hashlib.sha256(data).hexdigest() + '.json'
            rows = [row for row in rows if row[0] != name] + [(name, data, key, record['end_monotonic_ns'])]
            # Newest cohorts first; newest two records per exact cohort.
            rows.sort(key=lambda x: (x[3], x[0]), reverse=True)
            kept, counts, size = [], {}, 0
            for row in rows:
                k = row[2]
                if k is None or (k not in counts and len(counts) >= 128) or counts.get(k, 0) >= 2 or size + len(row[1]) > LIMIT: continue
                counts[k] = counts.get(k, 0) + 1; size += len(row[1]); kept.append(row)
            keep = {row[0] for row in kept}
            check_directory()
            for old, _, _, _ in rows:
                if old not in keep:
                    try: os.unlink(old, dir_fd=fd)
                    except FileNotFoundError: pass
            # A locked reader sees a whole file; a crash leaves no partial final name.
            if name in keep and name not in existing:
                tmp = '.pending-' + secrets.token_hex(16)
                out = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600, dir_fd=fd)
                try:
                    with os.fdopen(out, 'wb') as f: f.write(data)
                    try: os.link(tmp, name, src_dir_fd=fd, dst_dir_fd=fd, follow_symlinks=False)
                    except FileExistsError: pass
                finally: os.unlink(tmp, dir_fd=fd)
            check_directory()
            return name in keep
        finally: os.close(lock); os.close(parent)
    finally: os.close(fd)


def main():
    try:
        publish(sys.argv[1].encode(), os.path.expanduser('~'))
    except Exception as e:
        print('heavy-observe: optional record publication failed: ' + str(e), file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__': sys.exit(main())
