/* Private selected-compiler cgroup. No sibling scopes or cap changes above it.
 * The single-command observer has no other children/concurrent child reaper.
 * Kernel/process namespaces and cgroup mounts must be native and unchanged. */
#include <poll.h>
#include <sys/stat.h>
#include <dirent.h>
#include <string.h>
#include <limits.h>

struct module_memory {
    uint64_t v[16], ancestors[64];
    size_t count;
    pid_t owner;
    int root, leaf, join, ack[2], release[2], subreaper, changed, created;
    char name[40], relative[PATH_MAX];
    uint64_t oom_before, kill_before;
};
struct memory_ack { uint64_t pid, inode, maximum, swap; int error; };

static int mm_decimal(char **cursor, uint64_t *out) {
    char *p = *cursor; uint64_t n = 0;
    if (*p < '0' || *p > '9') return EPROTO;
    while (*p >= '0' && *p <= '9') {
        unsigned digit = (unsigned)(*p++ - '0');
        if (n > (UINT64_MAX - digit) / 10) return EOVERFLOW;
        n = n * 10 + digit;
    }
    *cursor = p; *out = n; return 0;
}
static int mm_text(int dir, const char *name, const char *value) {
    int fd = openat(dir, name, O_WRONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return errno;
    size_t n = strlen(value); ssize_t k;
    do { k = write(fd, value, n); } while (k < 0 && errno == EINTR);
    int e = k == (ssize_t)n ? 0 : k < 0 ? errno : EIO;
    close(fd); return e;
}
static int mm_read(int dir, const char *name, char *buf, size_t n) {
    int fd = openat(dir, name, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return errno;
    ssize_t k; do { k = pread(fd, buf, n - 1, 0); } while (k < 0 && errno == EINTR);
    int e = k < 0 ? errno : (size_t)k == n - 1 ? EOVERFLOW : 0;
    if (!e) buf[k] = 0;
    close(fd); return e;
}
static int mm_number(int dir, const char *name, uint64_t *out, uint64_t unlimited) {
    char buf[128]; int e = mm_read(dir, name, buf, sizeof(buf));
    if (e) return e;
    if (!strcmp(buf, "max\n")) { *out = unlimited; return 0; }
    char *end = buf; e = mm_decimal(&end, out);
    if (e || (*end && strcmp(end, "\n"))) return e ? e : EPROTO;
    return 0;
}
static int mm_event(int dir, const char *file, const char *key, uint64_t *out) {
    char buf[1024], needle[64]; int e = mm_read(dir, file, buf, sizeof(buf));
    if (e) return e;
    snprintf(needle, sizeof(needle), "%s ", key);
    char *p = buf;
    while (p && *p) {
        if (!strncmp(p, needle, strlen(needle))) {
            char *end = p + strlen(needle); e = mm_decimal(&end, out);
            return e || (*end && *end != '\n') ? EPROTO : 0;
        }
        p = strchr(p, '\n'); if (p) ++p;
    }
    return EPROTO;
}
static int mm_location(char *out, size_t n) {
    char buf[PATH_MAX]; int e = mm_read(AT_FDCWD, "/proc/self/cgroup", buf, sizeof(buf));
    if (e) return e;
    if (strncmp(buf, "0::/", 4)) return ENOTSUP;
    char *end = strchr(buf, '\n');
    if (!end || end[1] || strstr(buf, "/../") || (size_t)(end - buf - 3) >= n) return EPROTO;
    memcpy(out, buf + 3, (size_t)(end - buf - 3)); out[end - buf - 3] = 0; return 0;
}
/* Baseline must be empty: this dedicated observer starts exactly one family.
 * Thereafter exact adopted children are that family's, independently of environ.
 * No waitpid(-1), numeric signals to adoptees, or other process migration. */
static int mm_children(int reap, int *remaining) {
    DIR *tasks = opendir("/proc/self/task"); if (!tasks) return errno;
    struct dirent *de; int error = 0; *remaining = 0;
    while ((de = readdir(tasks))) {
        if (de->d_name[0] < '0' || de->d_name[0] > '9') continue;
        char path[320], buf[32768];
        snprintf(path, sizeof(path), "/proc/self/task/%s/children", de->d_name);
        int e = mm_read(AT_FDCWD, path, buf, sizeof(buf));
        if (e) { error = e; break; }
        char *p = buf;
        while (*p) {
            char *end = p; uint64_t pid = 0;
            if (mm_decimal(&end, &pid) || pid == 0 || pid > INT_MAX) { error = EPROTO; break; }
            p = end; while (*p == ' ' || *p == '\n') ++p;
            if (reap) {
                int status; pid_t got = waitpid((pid_t)pid, &status, WNOHANG);
                if (got == (pid_t)pid) continue;
                if (got < 0 && errno != EINTR) { error = errno; break; }
            }
            ++*remaining;
        }
        if (error) break;
    }
    closedir(tasks); return error;
}
static void mm_init(struct module_memory *m, uint64_t requested) {
    memset(m, 0, sizeof(*m)); m->v[0] = requested; m->v[12] = 2;
    m->root = m->leaf = m->join = m->ack[0] = m->ack[1] = m->release[0] = m->release[1] = -1;
}
static int mm_root_identity(const char *root, pid_t owner) {
    const char *prefix = "/sys/fs/cgroup";
    if (!root || strncmp(root, prefix, strlen(prefix)) || strstr(root, "/../")) return EPERM;
    char current[PATH_MAX], expected[PATH_MAX]; int e = mm_location(current, sizeof(current));
    if (e) return e;
    const char *pool = strstr(root + strlen(prefix), "/heavy-modules-");
    if (!pool || strlen(pool) < 15 + 32 + 1) return EPERM;
    char token[33]; memcpy(token, pool + 15, 32); token[32]=0;
    for (int i=0;i<32;++i) if (!((token[i]>='0'&&token[i]<='9')||(token[i]>='a'&&token[i]<='f'))) return EPERM;
    char build[64]; snprintf(build,sizeof(build),"/build-%ld-",(long)owner);
    if (strncmp(pool+47,build,strlen(build)) || strlen(pool+47+strlen(build))!=32) return EPERM;
    for(const char *p=pool+47+strlen(build);*p;++p) if(!((*p>='0'&&*p<='9')||(*p>='a'&&*p<='f')))return EPERM;
    int n = snprintf(expected, sizeof(expected), "%.*s/heavy-driver-%s", (int)(pool-root-strlen(prefix)),root+strlen(prefix),token);
    if (n < 0 || (size_t)n >= sizeof(expected) || strcmp(current, expected)) return EPERM;
    return 0;
}
static int mm_prepare(struct module_memory *m) {
    if (!m->v[0]) return 0;
    if (m->v[0] > (1ULL << 50)) return EINVAL;
    const char *root = getenv("HEAVY_MODULE_MEMORY_ROOT");
    const char *prefix = "/sys/fs/cgroup";
    int e = mm_root_identity(root, m->owner);
    if (e) return e;
    m->root = open(root, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (m->root < 0) return errno;
    struct stat st; if (fstat(m->root, &st) < 0) return errno;
    if (st.st_uid != geteuid()) return EPERM;
    int parent = openat(m->root, "../..", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (parent < 0) return errno;
    e = mm_number(parent, "memory.max", &m->v[14], 0);
    if (!e && !m->v[14]) e = ENOTSUP;
    close(parent); if (e) return e;
    int live = 0; if ((e = mm_children(0, &live))) return e;
    if (live) return EBUSY;
    struct sigaction action;
    if (sigaction(SIGCHLD, NULL, &action) < 0) return errno;
    if (action.sa_handler != SIG_DFL || (action.sa_flags & SA_NOCLDWAIT)) return ENOTSUP;
    if (prctl(PR_GET_CHILD_SUBREAPER, &m->subreaper) < 0) return errno;
    if (!m->subreaper) { if (prctl(PR_SET_CHILD_SUBREAPER, 1) < 0) return errno; m->changed = 1; }
    uint64_t nonce;
    if (getrandom(&nonce, sizeof(nonce), GRND_NONBLOCK) != sizeof(nonce) || !nonce) return errno ? errno : EIO;
    m->v[13] = nonce; snprintf(m->name, sizeof(m->name), "m-%llu", (unsigned long long)nonce);
    if (mkdirat(m->root, m->name, 0700) < 0) return errno;
    m->created = 1;
    m->leaf = openat(m->root, m->name, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (m->leaf < 0) return errno;
    if (fstat(m->leaf, &st) < 0) return errno;
    m->v[7] = (uint64_t)st.st_ino;
    char text[64]; snprintf(text, sizeof(text), "%llu", (unsigned long long)m->v[0]);
    if ((e = mm_text(m->leaf, "memory.max", text)) || (e = mm_text(m->leaf, "memory.swap.max", "0")) ||
        (e = mm_text(m->leaf, "memory.oom.group", "1"))) return e;
    if ((e = mm_number(m->leaf, "memory.max", &m->v[2], 0)) ||
        (e = mm_number(m->leaf, "memory.swap.max", &m->v[3], UINT64_MAX))) return e;
    uint64_t group;
    if ((e = mm_number(m->leaf, "memory.oom.group", &group, 0))) return e;
    if (group != 1) return EPROTO;
    int ancestor = openat(m->leaf, "..", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    struct stat mount;
    if (stat(prefix, &mount) < 0) { if (ancestor >= 0) close(ancestor); return errno; }
    for (;;) {
        if (ancestor < 0) return errno;
        if (m->count == 64) { close(ancestor); return EOVERFLOW; }
        if (fstat(ancestor, &st) < 0) { e = errno; close(ancestor); return e; }
        if (st.st_ino == mount.st_ino && st.st_dev == mount.st_dev) { close(ancestor); break; }
        if ((e = mm_number(ancestor, "memory.max", &m->ancestors[m->count++], 0))) { close(ancestor); return e; }
        int next = openat(ancestor, "..", O_RDONLY | O_DIRECTORY | O_CLOEXEC); close(ancestor); ancestor = next;
    }
    if ((e = mm_event(m->leaf, "memory.events", "oom", &m->oom_before)) ||
        (e = mm_event(m->leaf, "memory.events", "oom_kill", &m->kill_before))) return e;
    int n = snprintf(m->relative, sizeof(m->relative), "%s/%s", root + strlen(prefix), m->name);
    if (n < 0 || (size_t)n >= sizeof(m->relative)) return ENAMETOOLONG;
    m->join = openat(m->leaf, "cgroup.procs", O_WRONLY | O_CLOEXEC);
    if (m->join < 0 || pipe2(m->ack, O_CLOEXEC | O_NONBLOCK) < 0 || pipe2(m->release, O_CLOEXEC) < 0) return errno;
    return 0;
}
/* Child uses only stack data and async-signal-safe syscalls. No Lean callback,
 * libc number parser, malloc or formatting occurs between fork and exec. */
static int mm_child(struct module_memory *m) {
    if (!m->v[0]) return 0;
    close(m->ack[0]); close(m->release[1]);
    struct memory_ack ack = {.pid = (uint64_t)getpid(), .maximum = m->v[2], .swap = m->v[3]};
    char decimal[32]; size_t size = 0; uint64_t pid = ack.pid;
    do { decimal[size++] = (char)('0' + pid % 10); pid /= 10; } while (pid);
    for (size_t i = 0; i < size / 2; ++i) { char c = decimal[i]; decimal[i] = decimal[size-i-1]; decimal[size-i-1] = c; }
    if (write(m->join, decimal, size) != (ssize_t)size) ack.error = errno ? errno : EIO;
    close(m->join);
    char buf[PATH_MAX]; int fd = open("/proc/self/cgroup", O_RDONLY | O_CLOEXEC);
    ssize_t n = fd < 0 ? -1 : read(fd, buf, sizeof(buf)-1);
    if (fd >= 0) close(fd);
    if (n < 0) ack.error = errno;
    else {
        buf[n] = 0; size_t k = 0;
        if (n < 5 || buf[0] != '0' || buf[1] != ':' || buf[2] != ':') ack.error = EPROTO;
        else {
            while (m->relative[k] && 3+k < (size_t)n && m->relative[k] == buf[3+k]) ++k;
            if (m->relative[k] || buf[3+k] != '\n' || 4+k != (size_t)n) ack.error = EXDEV;
            else { struct stat st; if (fstat(m->leaf, &st) < 0) ack.error = errno; else ack.inode = st.st_ino; }
        }
    }
    if (write(m->ack[1], &ack, sizeof(ack)) != sizeof(ack)) _exit(125);
    close(m->ack[1]);
    char go; ssize_t got;
    do { got = read(m->release[0], &go, 1); } while (got < 0 && errno == EINTR);
    close(m->release[0]);
    return got == 1 && go == '!' && !ack.error ? 0 : ack.error ? ack.error : ECANCELED;
}
static int mm_parent(struct module_memory *m, pid_t pid, b_lean_obj_arg control) {
    if (!m->v[0]) return 0;
    close(m->ack[1]); m->ack[1] = -1; close(m->release[0]); m->release[0] = -1;
    struct memory_ack ack; ssize_t n = -1;
    for (int i = 0; i < 100 && !budget_cancelled; ++i) {
        n = read(m->ack[0], &ack, sizeof(ack));
        if (n >= 0 || (errno != EAGAIN && errno != EINTR)) break;
        struct pollfd p = {.fd=m->ack[0], .events=POLLIN}; poll(&p, 1, 10);
    }
    if (n != sizeof(ack)) return budget_cancelled ? ECANCELED : ETIMEDOUT;
    m->v[6] = ack.pid; m->v[8] = ack.inode;
    if (ack.error) return ack.error;
    lean_object *raw = lean_alloc_array(0, 9+m->count);
    uint64_t fields[] = {4, 0, m->v[0], ack.maximum, ack.swap, (uint64_t)pid, ack.pid, m->v[7], ack.inode};
    for (size_t i=0;i<9;++i) raw=lean_array_push(raw,lean_box_uint64(fields[i]));
    for (size_t i=0;i<m->count;++i) raw=lean_array_push(raw,lean_box_uint64(m->ancestors[i]));
    lean_inc(control); lean_object *verdict=lean_apply_1(control,raw);
    if (lean_array_size(verdict)!=2) {lean_dec(verdict);return EPROTO;}
    uint64_t applied=lean_unbox_uint64(lean_array_get_core(verdict,0)), effective=lean_unbox_uint64(lean_array_get_core(verdict,1));
    lean_dec(verdict);
    if (applied!=m->v[0] || !effective || effective>applied) return EPROTO;
    if (budget_cancelled) return ECANCELED;
    if (write(m->release[1],"!",1)!=1) return errno ? errno : EIO;
    m->v[4]=applied;m->v[5]=effective;
    close(m->release[1]);m->release[1]=-1;return 0;
}
static void mm_finish(struct module_memory *m) {
    if (!m->v[0]) return;
    if (m->release[1]>=0) {close(m->release[1]);m->release[1]=-1;}
    if (m->leaf>=0) {
        int e=mm_text(m->leaf,"cgroup.kill","1");
        if (e) m->v[11]=e;
        for (int i=0;i<100;++i) {
            uint64_t populated=2;int remaining=0;
            e=mm_event(m->leaf,"cgroup.events","populated",&populated);
            if (e) {m->v[11]=e;break;}
            m->v[12]=populated;
            e=mm_children(1,&remaining);
            if (e) {m->v[11]=e;break;}
            if (!populated && !remaining) break;
            if (i==99) {m->v[11]=ETIMEDOUT;break;}
            struct timespec pause={0,10000000};nanosleep(&pause,NULL);
        }
        uint64_t n=0;
        e=mm_event(m->leaf,"memory.events","oom_kill",&n);
        if (e) m->v[11]=e; else m->v[9]=n>=m->kill_before?n-m->kill_before:0;
        e=mm_event(m->leaf,"memory.events","oom",&n);
        if (e) m->v[11]=e; else m->v[15]=n>=m->oom_before?n-m->oom_before:0;
        e=mm_number(m->leaf,"memory.peak",&m->v[10],0); if(e)m->v[11]=e;
    }
    if (m->join>=0) close(m->join);
    if (m->leaf>=0) close(m->leaf);
    if (m->root>=0 && m->created && unlinkat(m->root,m->name,AT_REMOVEDIR)<0) m->v[11]=errno;
    if (m->root>=0)close(m->root);
    for(int i=0;i<2;++i){if(m->ack[i]>=0)close(m->ack[i]);if(m->release[i]>=0)close(m->release[i]);}
    if(m->changed && prctl(PR_SET_CHILD_SUBREAPER,m->subreaper)<0)m->v[11]=errno;
}

static int mm_session_cleanup(pid_t owner) {
    const char *root=getenv("HEAVY_MODULE_MEMORY_ROOT");
    if(!root)return 0;
    int identity_error=mm_root_identity(root,owner);
    if(identity_error)return identity_error;
    char expected[64];snprintf(expected,sizeof(expected),"build-%ld-",(long)owner);
    const char *name=strrchr(root,'/');
    if(!name||strncmp(name+1,expected,strlen(expected))||strlen(name+1+strlen(expected))!=32)return EPERM;
    int dir=open(root,O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);
    if(dir<0)return errno==ENOENT?0:errno;
    struct stat st;if(fstat(dir,&st)<0||st.st_uid!=geteuid()){close(dir);return EPERM;}
    int copy=openat(dir,".",O_RDONLY|O_DIRECTORY|O_CLOEXEC);DIR *scan=copy<0?NULL:fdopendir(copy);
    if(!scan){int e=errno;if(copy>=0)close(copy);close(dir);return e;}
    struct timespec begin;
    if(clock_gettime(CLOCK_MONOTONIC,&begin)<0){int e=errno;closedir(scan);close(dir);return e;}
    int error=0;struct dirent *de;unsigned count=0;
    while((de=readdir(scan))) {
        if(strncmp(de->d_name,"m-",2))continue;
        if(++count>4096){error=EOVERFLOW;break;}
        for(const char *p=de->d_name+2;*p;++p)if(*p<'0'||*p>'9')error=EPROTO;
        if(error)break;
        int leaf=openat(dir,de->d_name,O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);
        if(leaf<0){if(errno==ENOENT)continue;error=errno;break;}
        int e=mm_text(leaf,"cgroup.kill","1");
        for(int i=0;!e&&i<100;++i){
            uint64_t populated=2;e=mm_event(leaf,"cgroup.events","populated",&populated);
            if(e||!populated)break;
            struct timespec now;
            if(clock_gettime(CLOCK_MONOTONIC,&now)<0){e=errno;break;}
            int64_t elapsed=(int64_t)(now.tv_sec-begin.tv_sec)*1000000000+now.tv_nsec-begin.tv_nsec;
            if(i==99||elapsed>=1000000000){e=ETIMEDOUT;break;}
            struct timespec pause={0,10000000};nanosleep(&pause,NULL);
        }
        close(leaf);
        if(!e&&unlinkat(dir,de->d_name,AT_REMOVEDIR)<0&&errno!=ENOENT)e=errno;
        if(e){error=e;break;}
    }
    closedir(scan);close(dir);
    if(!error&&rmdir(root)<0&&errno!=ENOENT)error=errno;
    return error;
}
