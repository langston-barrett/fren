#define _GNU_SOURCE
#include <lean/lean.h>
#include <signal.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
/* Isolate signal behavior using the implementation's current signature.
   ABI is checked separately against the actual generated declaration. */
extern lean_object *heavy_observe_notice(lean_object *);
static int inject, interrupt_wait, injected_external, injected_eintr, observed_errno;
static ssize_t observed_write;
ssize_t __real_write(int, const void *, size_t);
ssize_t __wrap_write(int fd, const void *s, size_t n) {
    if (fd == 2 && inject) { inject = 0; injected_external = 1; kill(getpid(), SIGPIPE); }
    ssize_t result = __real_write(fd, s, n);
    if (fd == 2) { observed_write = result; observed_errno = result < 0 ? errno : 0; }
    return result;
}
int __real_sigtimedwait(const sigset_t *, siginfo_t *, const struct timespec *);
int __wrap_sigtimedwait(const sigset_t *s, siginfo_t *info, const struct timespec *t) {
    if (interrupt_wait) { interrupt_wait = 0; injected_eintr = 1; errno = EINTR; return -1; }
    return __real_sigtimedwait(s, info, t);
}
static int pending_pipe(void) { sigset_t p; sigpending(&p); return sigismember(&p, SIGPIPE); }
int main(int argc, char **argv) {
    if (argc != 2) return 90;
    sigset_t set, before, after;
    sigemptyset(&set); sigaddset(&set, SIGPIPE);
    sigprocmask(SIG_BLOCK, &set, NULL);
    struct sigaction sa = {0}, disposition;
    sa.sa_handler = SIG_DFL; sigemptyset(&sa.sa_mask); sigaction(SIGPIPE, &sa, NULL);
    int closed = strcmp(argv[1], "unrelated-on-success") != 0;
    if (!strcmp(argv[1], "absent-stderr")) close(2);
    else if (!strcmp(argv[1], "full-device")) { int fd = open("/dev/full", O_WRONLY); dup2(fd, 2); close(fd); }
    else if (closed) { int p[2]; if (pipe(p)) return 91; close(p[0]); dup2(p[1], 2); close(p[1]); }
    else { int fd = open("/dev/null", O_WRONLY); dup2(fd, 2); close(fd); inject = 1; }
    if (!strcmp(argv[1], "preexisting")) kill(getpid(), SIGPIPE);
    if (!strcmp(argv[1], "interrupted-drain")) interrupt_wait = 1;
    int was = pending_pipe(); sigprocmask(SIG_SETMASK, NULL, &before);
    lean_object *s = lean_mk_string("bounded note\n");
    lean_object *result = heavy_observe_notice(s);
    int is = pending_pipe(); sigprocmask(SIG_SETMASK, NULL, &after);
    sigaction(SIGPIPE, NULL, &disposition);
    int mask_equal = 1;
    for (int i = 1; i < NSIG; i++) if (sigismember(&before, i) != sigismember(&after, i)) mask_equal = 0;
    printf("{\"case\":\"%s\",\"before_pending\":%d,\"after_pending\":%d,\"mask_preserved\":%d,\"default_disposition_preserved\":%d,\"io_ok\":%d}\n",
           argv[1], was, is, mask_equal, disposition.sa_handler == SIG_DFL, lean_io_result_is_ok(result));
    printf("{\"write_result\":%ld,\"write_errno\":%d,\"injected_external\":%d,\"injected_eintr\":%d}\n", (long)observed_write, observed_errno, injected_external, injected_eintr);
    lean_dec(s); lean_dec(result);
    return 0;
}
