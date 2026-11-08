#define _GNU_SOURCE
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include <sys/prctl.h>

extern char **environ;

/* Raw Linux observations only. All classification happens in Heavy.Process.
 * Slots: launch errno, exec errno, wait errno, clock errno, status, pid,
 * monotonic start/end ns, wait4 user/system us, wait4 maxrss KiB. */
static volatile sig_atomic_t budget_cancelled;
static void budget_signal(int sig) { budget_cancelled = sig; }

static lean_obj_res observe_wait(b_lean_obj_arg exe, b_lean_obj_arg args, int guarded, uint64_t cpu_limit) {
    uint64_t v[15] = {0};
    size_t n = lean_array_size(args);
    char **argv = calloc(n + 2, sizeof(char *));
    int pipefd[2] = {-1, -1};
    struct timespec t;
    if (!argv) { v[0] = ENOMEM; goto done; }
    if (guarded && budget_cancelled) { v[0] = ECANCELED; goto done; }
    argv[0] = (char *)lean_string_cstr(exe);
    for (size_t i = 0; i < n; ++i)
        argv[i + 1] = (char *)lean_string_cstr(lean_array_get_core(args, i));
    if (pipe2(pipefd, O_CLOEXEC) < 0) { v[0] = errno; goto done; }
    if (clock_gettime(CLOCK_MONOTONIC, &t) < 0) v[3] = errno;
    else v[6] = (uint64_t)t.tv_sec * 1000000000 + (uint64_t)t.tv_nsec;
    pid_t parent = getpid();
    pid_t pid = fork();
    if (pid < 0) { v[0] = errno; goto done; }
    if (pid == 0) {
        close(pipefd[0]);
        int e = 0, code = 127;
        if (guarded) {
            if (prctl(PR_SET_PDEATHSIG, SIGKILL) < 0) e = -errno;
            else if (getppid() != parent) e = -EOWNERDEAD;
        }
        if (!e && cpu_limit) {
            struct rlimit limit = {(rlim_t)cpu_limit, (rlim_t)cpu_limit};
            if (setrlimit(RLIMIT_CPU, &limit) < 0) e = -errno;
        }
        if (!e && cpu_limit) {
            int ack = 0x48435055;
            ssize_t n;
            do { n = write(pipefd[1], &ack, sizeof(ack)); } while (n < 0 && errno == EINTR);
            if (n != sizeof(ack)) _exit(125);
        }
        if (e) code = 125;
        else { execve(argv[0], argv, environ); e = errno; }
        /* Only async-signal-safe operations between fork and _exit. */
        const char *p = (const char *)&e;
        size_t left = sizeof(e);
        while (left) {
            ssize_t k = write(pipefd[1], p, left);
            if (k < 0 && errno == EINTR) continue;
            if (k <= 0) break;
            p += k; left -= (size_t)k;
        }
        _exit(code);
    }
    v[5] = (uint64_t)pid;
    close(pipefd[1]); pipefd[1] = -1;
    int status = 0;
    struct rusage usage = {0};
    pid_t waited;
    if (!guarded) {
        do { waited = wait4(pid, &status, 0, &usage); }
        while (waited < 0 && errno == EINTR);
    } else {
        unsigned cancelled_ticks = 0;
        for (;;) {
            waited = wait4(pid, &status, WNOHANG, &usage);
            if (waited != 0 && !(waited < 0 && errno == EINTR)) break;
            /* This PID is our unreaped child, so cannot be reused. */
            if (budget_cancelled) {
                if (cancelled_ticks == 0) kill(pid, SIGTERM);
                if (cancelled_ticks == 25) kill(pid, SIGKILL);
                if (cancelled_ticks >= 125) { errno = ETIMEDOUT; waited = -1; break; }
                ++cancelled_ticks;
            }
            struct timespec pause = {0, 10000000};
            nanosleep(&pause, NULL);
        }
    }
    if (waited < 0) v[2] = errno;
    else {
        v[4] = (unsigned int)status;
        v[8] = (uint64_t)usage.ru_utime.tv_sec * 1000000 + usage.ru_utime.tv_usec;
        v[9] = (uint64_t)usage.ru_stime.tv_sec * 1000000 + usage.ru_stime.tv_usec;
        v[10] = (uint64_t)usage.ru_maxrss;
    }
    if (clock_gettime(CLOCK_MONOTONIC, &t) < 0) v[3] = errno;
    else v[7] = (uint64_t)t.tv_sec * 1000000000 + (uint64_t)t.tv_nsec;
    int frames[2] = {0, 0};
    size_t used = 0;
    int read_error = 0, eof = 0;
    while (!guarded || waited >= 0) {
        char overflow;
        void *dst = used < sizeof(frames) ? (char *)frames + used : &overflow;
        size_t available = used < sizeof(frames) ? sizeof(frames) - used : 1;
        ssize_t k = read(pipefd[0], dst, available);
        if (k < 0 && errno == EINTR) continue;
        if (k < 0) { read_error = errno; break; }
        if (k == 0) { eof = 1; break; }
        if (used == sizeof(frames)) { read_error = EOVERFLOW; break; }
        used += (size_t)k;
    }
    v[11] = used; v[12] = (unsigned int)frames[0]; v[13] = read_error; v[14] = eof;
    if (read_error) v[2] = read_error;
    else if (used % sizeof(int)) v[2] = EIO;
    else {
        size_t offset = used && frames[0] == 0x48435055 ? 1 : 0;
        if (used / sizeof(int) > offset) {
            int exec_error = frames[offset];
            if (exec_error < 0) v[0] = (unsigned int)(-exec_error);
            else v[1] = (unsigned int)exec_error;
        }
    }

done:
    if (pipefd[0] >= 0) close(pipefd[0]);
    if (pipefd[1] >= 0) close(pipefd[1]);
    free(argv);
    lean_object *a = lean_alloc_array(0, 15);
    for (size_t i = 0; i < 15; ++i) a = lean_array_push(a, lean_box_uint64(v[i]));
    return lean_io_result_mk_ok(a);
}

LEAN_EXPORT lean_obj_res heavy_observe_wait(b_lean_obj_arg exe, b_lean_obj_arg args) {
    return observe_wait(exe, args, 0, 0);
}

/* Preserve a child's signal termination after Lean has flushed its record. */
LEAN_EXPORT lean_obj_res heavy_observe_signal(uint32_t sig) {
    struct sigaction sa = {0};
    sa.sa_handler = SIG_DFL;
    sigemptyset(&sa.sa_mask);
    sigaction((int)sig, &sa, NULL);
    sigset_t set;
    sigemptyset(&set); sigaddset(&set, (int)sig);
    sigprocmask(SIG_UNBLOCK, &set, NULL);
    kill(getpid(), (int)sig);
    _exit(128 + (int)sig);
}

#include <stdio.h>
#include <string.h>

/* Filesystem authenticity is an external assumption, tested by integration.
 * Publish only complete records; concurrent observers never share a file. */
LEAN_EXPORT lean_obj_res heavy_observe_write(b_lean_obj_arg dir,
                                            b_lean_obj_arg record) {
    const char *d = lean_string_cstr(dir);
    const char *r = lean_string_cstr(record);
    char *tmp = NULL, *final = NULL;
    int error = 0;
    if (asprintf(&tmp, "%s/.process-XXXXXX", d) < 0) { error = ENOMEM; goto done; }
    int fd = mkstemp(tmp);
    if (fd < 0) { error = errno; goto done; }
    size_t left = strlen(r);
    while (left) {
        ssize_t k = write(fd, r, left);
        if (k < 0 && errno == EINTR) continue;
        if (k <= 0) { error = k < 0 ? errno : EIO; break; }
        r += k; left -= (size_t)k;
    }
    if (!error && write(fd, "\n", 1) != 1) error = errno ? errno : EIO;
    if (close(fd) < 0 && !error) error = errno;
    if (!error && asprintf(&final, "%s/process-%s.json", d, strrchr(tmp, '-') + 1) < 0)
        error = ENOMEM;
    /* Do not overwrite a previous record if a random suffix is reused. */
    if (!error && link(tmp, final) < 0) error = errno;
    unlink(tmp);
done:
    free(tmp); free(final);
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)error));
}

#include <sys/stat.h>

/* O_PATH pins identity without opening a FIFO as a reader (even a nonblocking
 * read-open can wake its producer). Only after the actual Lean eligibility
 * callback do we open the pinned regular object via procfs, not its pathname. */
LEAN_EXPORT lean_obj_res heavy_observe_read_regular(b_lean_obj_arg path,
                                                   b_lean_obj_arg accept) {
    int pinned = open(lean_string_cstr(path), O_PATH | O_CLOEXEC);
    if (pinned < 0) return lean_io_result_mk_ok(lean_box(0));
    struct stat st;
    if (fstat(pinned, &st) < 0) { close(pinned); return lean_io_result_mk_ok(lean_box(0)); }
    lean_inc(accept);
    lean_object *allowed = lean_apply_2(accept, lean_uint64_to_nat((uint64_t)st.st_mode),
                                        lean_uint64_to_nat((uint64_t)st.st_size));
    bool ok = lean_unbox(allowed);
    lean_dec(allowed);
    if (!ok) { close(pinned); return lean_io_result_mk_ok(lean_box(0)); }
    char procpath[64];
    snprintf(procpath, sizeof(procpath), "/proc/self/fd/%d", pinned);
    int fd = open(procpath, O_RDONLY | O_CLOEXEC);
    struct stat reopened;
    if (fd < 0 || fstat(fd, &reopened) < 0 ||
        st.st_dev != reopened.st_dev || st.st_ino != reopened.st_ino) {
        if (fd >= 0) close(fd);
        close(pinned);
        return lean_io_result_mk_ok(lean_box(0));
    }
    close(pinned);
    size_t size = (size_t)st.st_size, at = 0;
    lean_object *bytes = lean_alloc_sarray(1, size, size);
    while (at < size) {
        ssize_t k = read(fd, lean_sarray_cptr(bytes) + at, size - at);
        if (k < 0 && errno == EINTR) continue;
        if (k <= 0) { ok = false; break; }
        at += (size_t)k;
    }
    char extra;
    ssize_t end;
    do { end = read(fd, &extra, 1); } while (end < 0 && errno == EINTR);
    if (end != 0) ok = false; /* A growing file or a pseudo-file is incomplete. */
    if (close(fd) < 0) ok = false;
    if (!ok) { lean_dec(bytes); return lean_io_result_mk_ok(lean_box(0)); }
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, bytes);
    return lean_io_result_mk_ok(some);
}

#include "budget.c"
