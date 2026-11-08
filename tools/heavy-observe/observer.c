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

extern char **environ;

/* Raw Linux observations only. All classification happens in Heavy.Process.
 * Slots: launch errno, exec errno, wait errno, clock errno, status, pid,
 * monotonic start/end ns, wait4 user/system us, wait4 maxrss KiB. */
LEAN_EXPORT lean_obj_res heavy_observe_wait(b_lean_obj_arg exe,
                                           b_lean_obj_arg args,
                                           lean_obj_arg world) {
    (void)world;
    uint64_t v[11] = {0};
    size_t n = lean_array_size(args);
    char **argv = calloc(n + 2, sizeof(char *));
    int pipefd[2] = {-1, -1};
    struct timespec t;
    if (!argv) { v[0] = ENOMEM; goto done; }
    argv[0] = (char *)lean_string_cstr(exe);
    for (size_t i = 0; i < n; ++i)
        argv[i + 1] = (char *)lean_string_cstr(lean_array_get_core(args, i));
    if (pipe2(pipefd, O_CLOEXEC) < 0) { v[0] = errno; goto done; }
    if (clock_gettime(CLOCK_MONOTONIC, &t) < 0) v[3] = errno;
    else v[6] = (uint64_t)t.tv_sec * 1000000000 + (uint64_t)t.tv_nsec;
    pid_t pid = fork();
    if (pid < 0) { v[0] = errno; goto done; }
    if (pid == 0) {
        close(pipefd[0]);
        execve(argv[0], argv, environ);
        int e = errno;
        /* Only async-signal-safe operations between fork and _exit. */
        const char *p = (const char *)&e;
        size_t left = sizeof(e);
        while (left) {
            ssize_t k = write(pipefd[1], p, left);
            if (k < 0 && errno == EINTR) continue;
            if (k <= 0) break;
            p += k; left -= (size_t)k;
        }
        _exit(127);
    }
    v[5] = (uint64_t)pid;
    close(pipefd[1]); pipefd[1] = -1;
    int status = 0;
    struct rusage usage = {0};
    pid_t waited;
    do { waited = wait4(pid, &status, 0, &usage); }
    while (waited < 0 && errno == EINTR);
    if (waited < 0) v[2] = errno;
    else {
        v[4] = (unsigned int)status;
        v[8] = (uint64_t)usage.ru_utime.tv_sec * 1000000 + usage.ru_utime.tv_usec;
        v[9] = (uint64_t)usage.ru_stime.tv_sec * 1000000 + usage.ru_stime.tv_usec;
        v[10] = (uint64_t)usage.ru_maxrss;
    }
    if (clock_gettime(CLOCK_MONOTONIC, &t) < 0) v[3] = errno;
    else v[7] = (uint64_t)t.tv_sec * 1000000000 + (uint64_t)t.tv_nsec;
    int exec_error = 0;
    size_t used = 0;
    while (used < sizeof(exec_error)) {
        ssize_t k = read(pipefd[0], (char *)&exec_error + used, sizeof(exec_error) - used);
        if (k < 0 && errno == EINTR) continue;
        if (k < 0) { v[2] = errno; break; }
        if (k == 0) break;
        used += (size_t)k;
    }
    if (used == sizeof(exec_error)) v[1] = (unsigned int)exec_error;
    else if (used) v[2] = EIO;
done:
    if (pipefd[0] >= 0) close(pipefd[0]);
    if (pipefd[1] >= 0) close(pipefd[1]);
    free(argv);
    lean_object *a = lean_alloc_array(0, 11);
    for (size_t i = 0; i < 11; ++i) a = lean_array_push(a, lean_box_uint64(v[i]));
    return lean_io_result_mk_ok(a);
}

/* Preserve a child's signal termination after Lean has flushed its record. */
LEAN_EXPORT lean_obj_res heavy_observe_signal(uint32_t sig, lean_obj_arg world) {
    (void)world;
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
                                            b_lean_obj_arg record,
                                            lean_obj_arg world) {
    (void)world;
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

/* Inspect the opened file, not a racy pathname stat followed by a blocking
 * reopen. The actual Lean policy decides from raw mode/size before any read. */
LEAN_EXPORT lean_obj_res heavy_observe_read_regular(b_lean_obj_arg path,
                                                   b_lean_obj_arg accept,
                                                   lean_obj_arg world) {
    (void)world;
    int fd = open(lean_string_cstr(path), O_RDONLY | O_NONBLOCK | O_CLOEXEC);
    if (fd < 0) return lean_io_result_mk_ok(lean_box(0));
    struct stat st;
    if (fstat(fd, &st) < 0) { close(fd); return lean_io_result_mk_ok(lean_box(0)); }
    lean_inc(accept);
    lean_object *allowed = lean_apply_2(accept, lean_uint64_to_nat((uint64_t)st.st_mode),
                                        lean_uint64_to_nat((uint64_t)st.st_size));
    bool ok = lean_unbox(allowed);
    lean_dec(allowed);
    if (!ok) { close(fd); return lean_io_result_mk_ok(lean_box(0)); }
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
