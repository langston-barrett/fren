#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

/* Test-only interposition: preserve real IO/clock/lock results. Pauses hold
 * an actual snapshot or publication open. No hooks are linked into Heavy. */
static void event(const char *kind, long a, long b, long c) {
    const char *path = getenv("BOUNDARY_LOG");
    if (!path) return;
    int saved = errno;
    int fd = open(path, O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC, 0600);
    if (fd >= 0) {
        char text[256];
        int n = snprintf(text, sizeof(text), "{\"pid\":%ld,\"event\":\"%s\",\"a\":%ld,\"b\":%ld,\"c\":%ld}\n",
                         (long)getpid(), kind, a, b, c);
        if (n > 0 && (size_t)n < sizeof(text)) syscall(SYS_write, fd, text, (size_t)n);
        close(fd);
    }
    errno = saved;
}
static int target(int fd) {
    const char *path = getenv("BOUNDARY_TARGET");
    struct stat a, b;
    return path && stat(path, &a) == 0 && fstat(fd, &b) == 0 &&
        a.st_dev == b.st_dev && a.st_ino == b.st_ino;
}
static void pause_once(void) {
    static int paused;
    const char *ready = getenv("BOUNDARY_READY"), *resume = getenv("BOUNDARY_RESUME");
    if (paused || !ready || !resume) return;
    paused = 1;
    int fd = open(ready, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0600);
    if (fd >= 0) close(fd);
    event("pause", 0, 0, 0);
    struct timespec begin, now, delay = {0, 1000000};
    clock_gettime(CLOCK_MONOTONIC, &begin);
    for (;;) {
        if (access(resume, F_OK) == 0) break;
        clock_gettime(CLOCK_MONOTONIC, &now);
        if (now.tv_sec - begin.tv_sec >= 2) _exit(124);
        nanosleep(&delay, NULL);
    }
}
ssize_t pread(int fd, void *buf, size_t count, off_t offset) {
    ssize_t result = syscall(SYS_pread64, fd, buf, count, offset);
    int saved = errno;
    if (getenv("BOUNDARY_SNAPSHOT") && result > 0 && target(fd)) pause_once();
    errno = saved; return result;
}
ssize_t write(int fd, const void *buf, size_t count) {
    ssize_t result = syscall(SYS_write, fd, buf, count);
    int saved = errno;
    /* Running state, not the earlier waiting-row publication. */
    if (getenv("BOUNDARY_GRANT") && result > 0 && count >= 4 &&
        memmem(buf, count, " 1 ", 3) && target(fd)) pause_once();
    errno = saved; return result;
}

static void custom_chld(int signal) { (void)signal; }
static unsigned queries;
int sigaction(int sig, const struct sigaction *act, struct sigaction *old) {
    int (*real_action)(int, const struct sigaction *, struct sigaction *) = dlsym(RTLD_NEXT, "sigaction");
    if (sig == SIGCHLD && !act) {
        ++queries;
        if (getenv("BOUNDARY_QUERY_ERROR") || (getenv("BOUNDARY_LAST_QUERY_ERROR") && queries == 3)) {
            event("query-error", queries, EIO, 0); errno = EIO; return -1;
        }
    }
    int result = real_action(sig, act, old);
    if (sig == SIGCHLD && !act && result == 0)
        event("query", (long)(uintptr_t)old->sa_handler, (unsigned)old->sa_flags, SA_NOCLDWAIT);
    return result;
}
__attribute__((constructor)) static void disposition(void) {
    const char *mode = getenv("BOUNDARY_CHLD");
    if (!mode) return;
    int (*real_action)(int, const struct sigaction *, struct sigaction *) = dlsym(RTLD_NEXT, "sigaction");
    struct sigaction sa = {0}; sigemptyset(&sa.sa_mask);
    sa.sa_handler = !strcmp(mode, "ignore") ? SIG_IGN : !strcmp(mode, "custom") ? custom_chld : SIG_DFL;
    sa.sa_flags = !strcmp(mode, "auto") ? SA_NOCLDWAIT : 0;
    if (strcmp(mode, "inherited") && real_action(SIGCHLD, &sa, NULL) < 0) _exit(123);
    if (real_action(SIGCHLD, NULL, &sa) < 0) _exit(123);
    event("disposition", (long)(uintptr_t)sa.sa_handler, (unsigned)sa.sa_flags, SA_NOCLDWAIT);
}
pid_t fork(void) {
    pid_t (*real_fork)(void) = dlsym(RTLD_NEXT, "fork");
    pid_t child = real_fork();
    if (child > 0) event("fork", child, 0, 0);
    return child;
}
int waitid(idtype_t type, id_t id, siginfo_t *info, int options) {
    int result = syscall(SYS_waitid, type, id, info, options, NULL);
    if (getenv("BOUNDARY_REAP") && result == 0 && type == P_PID && info->si_pid && (options & WNOWAIT)) {
        int status = 0;
        pid_t reaped = syscall(SYS_wait4, id, &status, WNOHANG, NULL);
        event("reaped", reaped, status, 0);
        if (reaped == (pid_t)id) { errno = ECHILD; return -1; }
    }
    return result;
}
int kill(pid_t pid, int sig) {
    if (pid < 0 && getenv("BOUNDARY_GROUP_GUARD")) {
        /* Never deliver a negative-PID signal in this harmless true-child
         * fixture, even when testing the old unpinned cleanup. No PID reuse
         * is forced. Query only our own wait relationship, then suppress. */
        siginfo_t info = {0};
        int result = syscall(SYS_waitid, P_PID, (id_t)-pid, &info, WEXITED | WNOHANG | WNOWAIT, NULL);
        int error = result < 0 ? errno : 0;
        event("group-attempt", -pid, sig, error);
        errno = ESRCH; return -1;
    }
    return syscall(SYS_kill, pid, sig);
}
