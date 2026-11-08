/* Single-use, owned build sessions. Included by observer.c to share the real
 * fork/exec/wait4 path. No machine registry, daemon or memory measurement here. */
#include <dirent.h>
#include <limits.h>
#include <sys/file.h>

/* Decimal wire quantities avoid libc's version-specific scanf ABI and reject
 * signs, overflow and trailing non-whitespace rather than wrapping. */
static int budget_number(char **cursor, unsigned long long *value) {
    char *p = *cursor; unsigned long long n = 0;
    if (*p < '0' || *p > '9') return EPROTO;
    while (*p >= '0' && *p <= '9') {
        unsigned digit = (unsigned)(*p++ - '0');
        if (n > (ULLONG_MAX - digit) / 10) return EOVERFLOW;
        n = n * 10 + digit;
    }
    if (*p && *p != ' ' && *p != '\n') return EPROTO;
    while (*p == ' ' || *p == '\n') ++p;
    *value = n; *cursor = p; return 0;
}
static uint64_t budget_now(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t) < 0) return 0;
    return (uint64_t)t.tv_sec * 1000000000 + t.tv_nsec;
}
static int budget_text(int fd, const char *s) {
    size_t n = strlen(s), at = 0;
    if (ftruncate(fd, 0) < 0 || lseek(fd, 0, SEEK_SET) < 0) return errno;
    while (at < n) {
        ssize_t k = write(fd, s + at, n - at);
        if (k < 0 && errno == EINTR) continue;
        if (k <= 0) return k < 0 ? errno : EIO;
        at += (size_t)k;
    }
    return 0;
}
static int budget_read(int fd, char *buf, size_t size) {
    ssize_t n = pread(fd, buf, size - 1, 0);
    if (n < 0) return errno;
    if ((size_t)n == size - 1) return EOVERFLOW;
    buf[n] = 0;
    return 0;
}
static int budget_file(int dir, const char *name, int flags) {
    int fd = openat(dir, name, flags | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK, 0600);
    struct stat st;
    if (fd < 0) return -1;
    if (fstat(fd, &st) < 0 || !S_ISREG(st.st_mode) || st.st_uid != geteuid() ||
        st.st_nlink != 1 || (st.st_mode & 077) != 0) {
        close(fd); errno = EPERM; return -1;
    }
    return fd;
}
/* Reject ancestor-mounted procfs instead of resolving namespace-local PIDs
 * in the wrong view. Boot and namespace are part of space, not PID alone. */
static int budget_identity(pid_t pid, char *out, size_t size) {
    char path[80], text[4096], boot[80], *end, *token;
    snprintf(path, sizeof(path), "/proc/%ld/stat", (long)pid);
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return errno;
    int e = budget_read(fd, text, sizeof(text)); close(fd);
    if (e) return e;
    char *cursor = text; unsigned long long wire_pid;
    if (budget_number(&cursor, &wire_pid) || wire_pid != (unsigned long long)pid ||
        !(end = strrchr(text, ')'))) return EPROTO;
    unsigned long long start = 0;
    char *save = NULL;
    token = strtok_r(end + 2, " ", &save);
    for (int field = 3; token; ++field, token = strtok_r(NULL, " ", &save)) {
        if (field == 22) { if (budget_number(&token, &start)) return EPROTO; break; }
    }
    if (!start) return EPROTO;
    snprintf(path, sizeof(path), "/proc/%ld/ns/pid", (long)pid);
    struct stat ns;
    if (stat(path, &ns) < 0) return errno;
    fd = open("/proc/sys/kernel/random/boot_id", O_RDONLY | O_CLOEXEC);
    if (fd < 0) return errno;
    e = budget_read(fd, boot, sizeof(boot)); close(fd);
    if (e) return e;
    boot[strcspn(boot, "\n")] = 0;
    if (!boot[0]) return EPROTO;
    int n = snprintf(out, size, "%ld %llu %s:%llu:%llu", (long)pid, start, boot,
                     (unsigned long long)ns.st_dev, (unsigned long long)ns.st_ino);
    return n < 0 || (size_t)n >= size ? EOVERFLOW : 0;
}
static int budget_self(char *out, size_t size) {
    char text[4096];
    int fd = open("/proc/self/stat", O_RDONLY | O_CLOEXEC);
    if (fd < 0) return errno;
    int e = budget_read(fd, text, sizeof(text)); close(fd);
    if (e) return e;
    char *cursor = text; unsigned long long wire_pid;
    if (budget_number(&cursor, &wire_pid) || wire_pid != (unsigned long long)getpid()) return ENOTSUP;
    return budget_identity(getpid(), out, size);
}
static int budget_handlers(struct sigaction old[3], int install) {
    int sigs[] = {SIGINT, SIGTERM, SIGHUP};
    struct sigaction sa = {0}; sa.sa_handler = budget_signal; sigemptyset(&sa.sa_mask);
    for (int i = 0; i < 3; ++i) {
        if (install && sigaction(sigs[i], &sa, &old[i]) < 0) {
            int e = errno;
            while (i > 0) { --i; sigaction(sigs[i], &old[i], NULL); }
            return e;
        }
        if (!install && sigaction(sigs[i], &old[i], NULL) < 0) return errno;
    }
    return 0;
}
/* Invoke the shared Std-only control kernel on raw observations. */
static int budget_control(b_lean_obj_arg control, uint64_t *values, size_t count,
                          size_t outputs, size_t index, uint64_t *answer) {
    lean_object *raw = lean_alloc_array(0, count);
    for (size_t i = 0; i < count; ++i) raw = lean_array_push(raw, lean_box_uint64(values[i]));
    lean_inc(control);
    lean_object *result = lean_apply_1(control, raw);
    if (lean_array_size(result) != outputs) { lean_dec(result); return EPROTO; }
    *answer = lean_unbox_uint64(lean_array_get_core(result, index));
    lean_dec(result); return 0;
}
static int budget_deadline(b_lean_obj_arg control, uint64_t limit, uint64_t *sample) {
    struct timespec t;
    uint64_t error = 0;
    *sample = 0;
    if (clock_gettime(CLOCK_MONOTONIC, &t) < 0) error = errno;
    else *sample = (uint64_t)t.tv_sec * 1000000000 + (uint64_t)t.tv_nsec;
    uint64_t raw[] = {0, error, *sample, limit}, answer;
    int e = budget_control(control, raw, 4, 1, 0, &answer);
    if (e) return e;
    return answer == 0 ? 0 : answer == 1 ? ETIMEDOUT : answer == 2 ? (error ? (int)error : EIO) : EPROTO;
}
static int budget_lifecycle(b_lean_obj_arg control, int previous, int wait_error,
                            pid_t observed, pid_t expected, pid_t reaped, size_t output) {
    struct sigaction action = {0};
    int error = sigaction(SIGCHLD, NULL, &action) < 0 ? errno : 0;
    uint64_t raw[] = {1, (uint64_t)error, (uint64_t)(uintptr_t)action.sa_handler,
        (unsigned)action.sa_flags, SA_NOCLDWAIT, (uint64_t)previous, (uint64_t)wait_error,
        (uint64_t)observed, (uint64_t)expected, (uint64_t)reaped}, answer;
    int e = budget_control(control, raw, 10, 2, output, &answer);
    if (e) return e;
    if (answer == 1) return 0;
    if (answer != 0) return EPROTO;
    return error ? error : previous ? previous : wait_error ? wait_error : ENOTSUP;
}
static int budget_group_signal(b_lean_obj_arg control, pid_t child, int signal,
                               int previous, pid_t reaped) {
    siginfo_t info = {0};
    int error = waitid(P_PID, (id_t)child, &info, WEXITED | WNOHANG | WNOWAIT) < 0 ? errno : 0;
    int e = budget_lifecycle(control, previous, error, info.si_pid, child, reaped, 1);
    if (e) return e;
    if (kill(-child, signal) < 0 && errno != ESRCH) return errno;
    return 0;
}
static int budget_lock(b_lean_obj_arg control, int fd, uint64_t deadline) {
    for (;;) {
        if (budget_cancelled) return ECANCELED;
        uint64_t now;
        int e = budget_deadline(control, deadline, &now);
        if (e) return e;
        if (flock(fd, LOCK_EX | LOCK_NB) == 0) {
            /* Acquisition itself can be preempted across the deadline. */
            e = budget_deadline(control, deadline, &now);
            if (e && flock(fd, LOCK_UN) < 0) return errno;
            return e;
        }
        if (errno != EAGAIN && errno != EWOULDBLOCK) return errno;
        struct timespec pause = {0, 10000000}; nanosleep(&pause, NULL);
    }
}
/* callback receives raw config/header then raw locked rows. Each row contains
 * stored ticket/state/demand/owner and an independent procfs observation.
 * No ownership/fit Boolean is supplied to Lean. */
LEAN_EXPORT lean_obj_res heavy_budget_observe(b_lean_obj_arg exe, b_lean_obj_arg args,
    b_lean_obj_arg path, uint64_t demand, b_lean_obj_arg decide, b_lean_obj_arg control) {
    uint64_t extra[7] = {0}; /* error, admission wait ns, ticket, held, allowance, parent */
    lean_object *result = NULL;
    int dir = -1, registry = -1, owner = -1, ticketfd = -1, counter = -1, config = -1;
    int locked = 0, e = 0, handlers = 0;
    char self[256], owner_text[512], observed[256], buf[1024], name[80] = {0};
    unsigned long long allowance, parent, fallback, wait_ms, next, group;
    long owner_pid;
    uint64_t begin = budget_now(), deadline = 0;
    struct sigaction old[3]; budget_cancelled = 0;
    if ((e = budget_lifecycle(control, 0, 0, 0, 0, 0, 0))) goto done;
    if ((e = budget_handlers(old, 1))) goto done;
    handlers = 1;
    if (!begin) { e = EIO; goto done; }
    if ((e = budget_self(self, sizeof(self)))) goto done;
    pid_t caller_parent = getppid();
    if (caller_parent <= 1 || getpgid(caller_parent) != getpgrp()) { e = EPERM; goto done; }
    if (prctl(PR_SET_PDEATHSIG, SIGKILL) < 0) { e = errno; goto done; }
    if (getppid() != caller_parent) { e = EOWNERDEAD; goto done; }
    dir = open(lean_string_cstr(path), O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    struct stat st;
    if (dir < 0) { e = errno; goto done; }
    if (fstat(dir, &st) < 0 || st.st_uid != geteuid() || (st.st_mode & 077) != 0) { e = EPERM; goto done; }
    owner = budget_file(dir, "owner", O_RDWR);
    registry = budget_file(dir, "registry", O_RDWR);
    config = budget_file(dir, "config", O_RDONLY);
    counter = budget_file(dir, "counter", O_RDWR);
    if (owner < 0 || registry < 0 || config < 0 || counter < 0) { e = errno; goto done; }
    if ((e = budget_read(config, buf, sizeof(buf)))) goto done;
    char *cursor = buf;
    if (budget_number(&cursor, &allowance) || budget_number(&cursor, &parent) ||
        budget_number(&cursor, &fallback) || budget_number(&cursor, &wait_ms) ||
        *cursor || allowance > (1ULL << 50) || parent > (1ULL << 50) ||
        fallback > (1ULL << 50) || wait_ms == 0 || wait_ms > 600000) { e = EINVAL; goto done; }
    extra[4] = allowance; extra[5] = parent;
    deadline = begin + wait_ms * 1000000;
    if (deadline < begin) { e = EOVERFLOW; goto done; }
    if ((e = budget_lock(control, registry, deadline))) goto done;
    locked = 1;
    if ((e = budget_read(counter, buf, sizeof(buf)))) goto done;
    cursor = buf;
    if (budget_number(&cursor, &next) || *cursor || next == 0 || next >= (1ULL << 50)) { e = EINVAL; goto done; }
    snprintf(buf, sizeof(buf), "%llu\n", next + 1);
    if ((e = budget_text(counter, buf))) goto done;
    extra[2] = next;
    snprintf(name, sizeof(name), "ticket-%020llu", next);
    ticketfd = budget_file(dir, name, O_RDWR | O_CREAT | O_EXCL);
    if (ticketfd < 0) { e = errno; goto done; }
    if (flock(ticketfd, LOCK_EX | LOCK_NB) < 0) { e = errno; goto done; }
    /* Child inherits this lock across exec; parent closes only its own fd. */
    if (fcntl(ticketfd, F_SETFD, 0) < 0) { e = errno; goto done; }
    snprintf(buf, sizeof(buf), "%llu 0 %llu %s\n", next, (unsigned long long)demand, self);
    if ((e = budget_text(ticketfd, buf))) goto done;
    for (;;) {
        if (!locked) {
            if ((e = budget_lock(control, registry, deadline))) goto done;
            locked = 1;
        }
        /* Session identity is checked every snapshot; unlocked/dead owners
         * retire the session. Never take over or repair another owner's row. */
        if (flock(owner, LOCK_EX | LOCK_NB) == 0) { e = EOWNERDEAD; goto done; }
        if (errno != EWOULDBLOCK && errno != EAGAIN) { e = errno; goto done; }
        if ((e = budget_read(owner, owner_text, sizeof(owner_text)))) goto done;
        char expected[256];
        cursor = owner_text;
        if (budget_number(&cursor, &group) || strlen(cursor) >= sizeof(expected) ||
            group != (unsigned long long)getpgrp()) { e = EPERM; goto done; }
        strcpy(expected, cursor); expected[strcspn(expected, "\n")] = 0;
        unsigned long long wire_pid;
        if (budget_number(&cursor, &wire_pid) || wire_pid == 0 || wire_pid > INT_MAX) { e = EPROTO; goto done; }
        owner_pid = (long)wire_pid;
        if ((e = budget_identity((pid_t)owner_pid, observed, sizeof(observed)))) goto done;
        if (strcmp(expected, observed)) { e = EOWNERDEAD; goto done; }
        lean_object *rows = lean_alloc_array(0, 0);
        snprintf(buf, sizeof(buf), "%llu %llu %llu %llu", allowance, parent, next, (unsigned long long)demand);
        rows = lean_array_push(rows, lean_mk_string(buf));
        int scanfd = openat(dir, ".", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
        DIR *scan = scanfd < 0 ? NULL : fdopendir(scanfd);
        if (!scan) { e = errno; if (scanfd >= 0) close(scanfd); lean_dec(rows); goto done; }
        struct dirent *entry;
        errno = 0;
        while ((errno = 0, entry = readdir(scan))) {
            if (strncmp(entry->d_name, "ticket-", 7)) continue;
            int fd = budget_file(dir, entry->d_name, O_RDWR);
            if (fd < 0) { e = errno; break; }
            if (flock(fd, LOCK_EX | LOCK_NB) == 0) { close(fd); continue; }
            if (errno != EWOULDBLOCK && errno != EAGAIN) { e = errno; close(fd); break; }
            e = budget_read(fd, buf, sizeof(buf)); close(fd);
            if (e) break;
            buf[strcspn(buf, "\n")] = 0;
            unsigned long long rt, rs, rd, wire_pid;
            cursor = buf;
            if (budget_number(&cursor, &rt) || budget_number(&cursor, &rs) ||
                budget_number(&cursor, &rd) || budget_number(&cursor, &wire_pid) ||
                wire_pid == 0 || wire_pid > INT_MAX) { e = EPROTO; break; }
            pid_t pid = (pid_t)wire_pid;
            int identity_error = budget_identity((pid_t)pid, observed, sizeof(observed));
            /* Missing identity is raw absence; the Lean row function rejects it. */
            char line[1600];
            snprintf(line, sizeof(line), "%s\t%s", buf, identity_error ? "" : observed);
            rows = lean_array_push(rows, lean_mk_string(line));
            errno = 0;
        }
        if (!e && errno) e = errno;
        closedir(scan);
        if (e) { lean_dec(rows); goto done; }
        lean_inc(decide);
        lean_object *verdict = lean_apply_1(decide, rows);
        if (lean_array_size(verdict) != 2) { lean_dec(verdict); e = EPROTO; goto done; }
        uint64_t code = lean_unbox_uint64(lean_array_get_core(verdict, 0));
        extra[3] = lean_unbox_uint64(lean_array_get_core(verdict, 1));
        lean_dec(verdict);
        if (code == 2) { e = EPROTO; goto done; }
        if (code == 3) { e = E2BIG; goto done; }
        if (code > 3) { e = EPROTO; goto done; }
        if (budget_cancelled) { e = ECANCELED; goto done; }
        if (code == 1) {
            uint64_t now;
            if ((e = budget_deadline(control, deadline, &now))) goto done;
            snprintf(buf, sizeof(buf), "%llu 1 %llu %s\n", next, (unsigned long long)demand, self);
            if ((e = budget_text(ticketfd, buf))) goto done;
            /* Publication/decoding may cross expiry too. No child is started
             * unless this actual commit sample is still eligible. */
            if ((e = budget_deadline(control, deadline, &now))) goto done;
            extra[1] = now - begin; extra[6] = now;
            if (flock(registry, LOCK_UN) < 0) { e = errno; goto done; }
            locked = 0;
            result = observe_wait(exe, args, 1);
            if (budget_cancelled) e = ECANCELED;
            goto done;
        }
        if (flock(registry, LOCK_UN) < 0) { e = errno; goto done; }
        locked = 0;
        if (budget_cancelled) { e = ECANCELED; goto done; }
        uint64_t now;
        if ((e = budget_deadline(control, deadline, &now))) goto done;
        struct timespec pause = {0, 10000000}; nanosleep(&pause, NULL);
    }
done:
    /* Do not unlink a running lease: inherited child descriptors may still
     * own it. Unlocked metadata is harmless and the session is single-use. */
    if (ticketfd >= 0 && close(ticketfd) < 0 && !e) e = errno;
    if (locked && flock(registry, LOCK_UN) < 0 && !e) e = errno;
    if (registry >= 0) close(registry);
    if (owner >= 0) close(owner);
    if (counter >= 0) close(counter);
    if (config >= 0) close(config);
    if (dir >= 0) close(dir);
    if (handlers) { int restore = budget_handlers(old, 0); if (!e) e = restore; }
    if (!result) {
        lean_object *a = lean_alloc_array(0, 11);
        for (int i = 0; i < 11; ++i) a = lean_array_push(a, lean_box_uint64(0));
        result = lean_io_result_mk_ok(a);
    }
    lean_object *a = lean_io_result_get_value(result); lean_inc(a); lean_dec(result);
    extra[0] = e;
    if (!extra[1] && begin) { uint64_t now = budget_now(); if (now) extra[1] = now - begin; }
    for (int i = 0; i < 7; ++i) a = lean_array_push(a, lean_box_uint64(extra[i]));
    return lean_io_result_mk_ok(a);
}

/* A transient owner for exactly one controlled build process group.
 * Only a supported disposition and successful unreaped-child observations
 * permit numeric group signals. SIGCHLD disposition is never changed. */
LEAN_EXPORT lean_obj_res heavy_budget_session(b_lean_obj_arg path, b_lean_obj_arg config,
    b_lean_obj_arg requests, b_lean_obj_arg exe, b_lean_obj_arg args, b_lean_obj_arg control) {
    uint64_t values[3] = {0}; /* control errno, command raw status, cleanup errno */
    int dir = -1, owner = -1, fd = -1, pipefd[2] = {-1, -1};
    pid_t child = -1, last_reaped = 0;
    int previous_wait_error = 0;
    int handlers = 0;
    char **argv = NULL;
    char identity[256], text[512];
    struct sigaction old[3]; budget_cancelled = 0;
    values[0] = budget_lifecycle(control, 0, 0, 0, 0, 0, 0);
    if (values[0]) goto done;
    values[0] = budget_handlers(old, 1);
    if (values[0]) goto done;
    handlers = 1;
    size_t n = lean_array_size(args);
    argv = calloc(n + 2, sizeof(char *));
    if (!argv) { values[0] = ENOMEM; goto done; }
    argv[0] = (char *)lean_string_cstr(exe);
    for (size_t i = 0; i < n; ++i) argv[i+1] = (char *)lean_string_cstr(lean_array_get_core(args, i));
    values[0] = budget_self(identity, sizeof(identity));
    if (values[0]) goto done;
    /* No takeover, reuse, symlinked session or pre-existing directory. */
    if (mkdir(lean_string_cstr(path), 0700) < 0) { values[0] = errno; goto done; }
    dir = open(lean_string_cstr(path), O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (dir < 0) { values[0] = errno; goto done; }
    const char *names[] = {"config", "requests", "counter", "registry"};
    const char *contents[] = {lean_string_cstr(config), lean_string_cstr(requests), "1\n", ""};
    for (int i = 0; i < 4; ++i) {
        fd = budget_file(dir, names[i], O_WRONLY | O_CREAT | O_EXCL);
        if (fd < 0) { values[0] = errno; goto done; }
        values[0] = budget_text(fd, contents[i]);
        if (close(fd) < 0 && !values[0]) values[0] = errno;
        fd = -1;
        if (values[0]) goto done;
    }
    owner = budget_file(dir, "owner", O_RDWR | O_CREAT | O_EXCL);
    if (owner < 0 || flock(owner, LOCK_EX | LOCK_NB) < 0) { values[0] = errno; goto done; }
    if (pipe2(pipefd, O_CLOEXEC) < 0) { values[0] = errno; goto done; }
    if (setenv("HEAVY_BUDGET_DIR", lean_string_cstr(path), 1) < 0) { values[0] = errno; goto done; }
    pid_t parent = getpid();
    child = fork();
    if (child < 0) { values[0] = errno; goto done; }
    if (child == 0) {
        close(pipefd[1]);
        if (setpgid(0, 0) < 0 || prctl(PR_SET_PDEATHSIG, SIGKILL) < 0 || getppid() != parent) _exit(125);
        /* Wait until owner identity has been published, before any compiler. */
        char ready;
        if (read(pipefd[0], &ready, 1) != 1) _exit(125);
        close(pipefd[0]);
        execve(argv[0], argv, environ);
        _exit(127);
    }
    close(pipefd[0]); pipefd[0] = -1;
    if (setpgid(child, child) < 0 && errno != EACCES) { values[0] = errno; goto cleanup; }
    snprintf(text, sizeof(text), "%ld %s\n", (long)child, identity);
    values[0] = budget_text(owner, text);
    if (values[0]) goto cleanup;
    if (write(pipefd[1], "!", 1) != 1) { values[0] = errno ? errno : EIO; goto cleanup; }
    close(pipefd[1]); pipefd[1] = -1;
    for (;;) {
        siginfo_t info = {0};
        if (waitid(P_PID, (id_t)child, &info, WEXITED | WNOHANG | WNOWAIT) < 0) {
            if (errno == EINTR) continue;
            previous_wait_error = errno; values[0] = errno; break;
        }
        if (info.si_pid || budget_cancelled) break;
        struct timespec pause = {0, 10000000}; nanosleep(&pause, NULL);
    }
cleanup:
    /* Recheck raw disposition and waitid before EACH signal. An earlier
     * wait error remains disqualifying, even if a later probe succeeds. */
    if (child > 0) {
        values[2] = budget_group_signal(control, child, SIGTERM, previous_wait_error, last_reaped);
        if (!values[2]) {
            struct timespec pause = {0, 50000000}; nanosleep(&pause, NULL);
            values[2] = budget_group_signal(control, child, SIGKILL, previous_wait_error, last_reaped);
        }
        /* A killed task stuck in uninterruptible kernel IO may not reap in
         * time. Report timeout and retain the retired session, never hang. */
        uint64_t limit = budget_now() + 1000000000;
        int status = 0;
        for (;;) {
            pid_t got = waitpid(child, &status, WNOHANG);
            if (got == child) { last_reaped = got; values[1] = (unsigned)status; break; }
            if (got < 0 && errno != EINTR) { values[2] = errno; break; }
            uint64_t now = budget_now();
            if (!now || now >= limit) { values[2] = ETIMEDOUT; break; }
            struct timespec short_pause = {0, 10000000}; nanosleep(&short_pause, NULL);
        }
    }
    /* Retain all metadata. Cleanup succeeds only after every inherited lease
     * is unlocked; a stuck/escaped descendant yields a bounded control error. */
    if (child > 0 && dir >= 0) {
        uint64_t deadline = budget_now() + 1000000000;
        for (;;) {
            int scanfd = openat(dir, ".", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
            DIR *scan = scanfd < 0 ? NULL : fdopendir(scanfd);
            if (!scan) { values[2] = errno; if (scanfd >= 0) close(scanfd); break; }
            int held = 0; struct dirent *entry;
            while ((errno = 0, entry = readdir(scan))) {
                if (strncmp(entry->d_name, "ticket-", 7)) continue;
                int lease = budget_file(dir, entry->d_name, O_RDWR);
                if (lease < 0) { values[2] = errno; break; }
                if (flock(lease, LOCK_EX | LOCK_NB) < 0) {
                    if (errno == EAGAIN || errno == EWOULDBLOCK) held = 1;
                    else values[2] = errno;
                }
                close(lease);
                if (values[2]) break;
            }
            if (!values[2] && errno) values[2] = errno;
            closedir(scan);
            if (values[2] || !held) break;
            uint64_t now = budget_now();
            if (!now || now >= deadline) { values[2] = ETIMEDOUT; break; }
            struct timespec pause = {0, 10000000}; nanosleep(&pause, NULL);
        }
    }
    if (budget_cancelled && !values[0]) values[0] = ECANCELED;
done:
    if (pipefd[0] >= 0) close(pipefd[0]);
    if (pipefd[1] >= 0) close(pipefd[1]);
    if (fd >= 0) close(fd);
    if (owner >= 0) close(owner);
    if (dir >= 0) close(dir);
    free(argv);
    if (handlers) { int restore = budget_handlers(old, 0); if (!values[0]) values[0] = restore; }
    lean_object *out = lean_alloc_array(0, 3);
    for (int i = 0; i < 3; ++i) out = lean_array_push(out, lean_box_uint64(values[i]));
    return lean_io_result_mk_ok(out);
}
