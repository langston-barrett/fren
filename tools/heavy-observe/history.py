"""Bounded read-only snapshot of the publisher's private raw store.

No forecast decisions: the actual observer decodes these bytes and applies the
Lean policy to its own compiler context. Contention or any invalid store means
unknown. Snapshotting once at session setup avoids scanning per compiler.
"""
import fcntl
import hashlib
import os
import stat

from publish import LIMIT, MAX_RECORD, NAME, decode, directory


def snapshot(home):
    fd = parent = lock = None
    try:
        if not os.path.isabs(home):
            return None
        fd = os.open('/', os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        for part in os.path.abspath(home).split('/')[1:] + ['.cache', 'heavy']:
            nxt = directory(fd, part)
            os.close(fd)
            fd = nxt
        parent = os.dup(fd)
        nxt = directory(fd, 'compiler-observations')
        os.close(fd)
        fd = nxt
        st = os.fstat(fd)
        if st.st_uid != os.geteuid() or stat.S_IMODE(st.st_mode) != 0o700:
            return None
        lock = os.open('.lock', os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC, dir_fd=fd)
        st = os.fstat(lock)
        if not stat.S_ISREG(st.st_mode) or st.st_uid != os.geteuid() or st.st_nlink != 1:
            return None
        fcntl.flock(lock, fcntl.LOCK_SH | fcntl.LOCK_NB)
        rows, size, entries = [], 0, 0
        with os.scandir(fd) as names:
            for entry in names:
                entries += 1
                if entries > 257:
                    return None
                name = entry.name
                if name == '.lock':
                    continue
                if not NAME.fullmatch(name):
                    return None
                rawfd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC, dir_fd=fd)
                try:
                    before = os.fstat(rawfd)
                    if (not stat.S_ISREG(before.st_mode) or before.st_uid != os.geteuid() or
                        before.st_nlink != 1 or stat.S_IMODE(before.st_mode) != 0o600 or
                        before.st_size > MAX_RECORD):
                        return None
                    data = os.read(rawfd, MAX_RECORD + 1)
                    after = os.fstat(rawfd)
                    if (len(data) != before.st_size or (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) !=
                        (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns) or
                        hashlib.sha256(data).hexdigest() + '.json' != name):
                        return None
                    # Reject duplicate fields/non-JSON constants, without
                    # duplicating the native eligibility/selection policy.
                    decode(data)
                finally:
                    os.close(rawfd)
                size += len(data)
                if size > LIMIT:
                    return None
                rows.append(data)
        named = os.stat('compiler-observations', dir_fd=parent, follow_symlinks=False)
        actual = os.fstat(fd)
        if (named.st_dev, named.st_ino) != (actual.st_dev, actual.st_ino):
            return None
        return b'[' + b','.join(rows) + b']'
    except (OSError, ValueError, UnicodeError, RecursionError):
        return None
    finally:
        for owned in (lock, parent, fd):
            if owned is not None:
                os.close(owned)
