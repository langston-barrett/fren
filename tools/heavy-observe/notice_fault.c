/* Test-only link wrappers: faults are injected, not observed OS failures. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
ssize_t __real_write(int, const void *, size_t);
static void mark(void) {
    const char *path = getenv("HEAVY_NOTICE_FAULT_MARKER");
    if (path) {
        int fd = open(path, O_WRONLY | O_CREAT | O_APPEND, 0600);
        if (fd >= 0) { (void)__real_write(fd, "x", 1); (void)close(fd); }
    }
}
ssize_t __wrap_write(int fd, const void *buf, size_t n) {
    const char *fault = getenv("HEAVY_NOTICE_FAULT");
    if (fd == 2 && n >= 15 && !memcmp(buf, "heavy-observe: ", 15) && fault) {
        if (!strcmp(fault, "EBADF")) { mark(); errno = EBADF; return -1; }
        if (!strcmp(fault, "ENOSPC")) { mark(); errno = ENOSPC; return -1; }
    }
    return __real_write(fd, buf, n);
}
int __real_sigtimedwait(const sigset_t *, siginfo_t *, const struct timespec *);
int __wrap_sigtimedwait(const sigset_t *s, siginfo_t *i, const struct timespec *t) {
    static int injected;
    const char *fault = getenv("HEAVY_NOTICE_FAULT");
    if (!injected && fault && !strcmp(fault, "EINTR")) {
        injected = 1; mark(); errno = EINTR; return -1;
    }
    return __real_sigtimedwait(s, i, t);
}
