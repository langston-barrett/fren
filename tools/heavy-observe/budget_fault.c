#define _GNU_SOURCE
#include <errno.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <unistd.h>
#include <stdarg.h>
#include <sys/prctl.h>

static pid_t initial_pid;
__attribute__((constructor)) static void capture_pid(void) { initial_pid = getpid(); }

/* Test-only fault at the actual gate's counter write. Match its inode, not
 * an fd number; no runtime injection switch is compiled into Heavy. */
ssize_t write(int fd, const void *buf, size_t count) {
    const char *target = getenv("BUDGET_FAIL_WRITE");
    struct stat expected, actual;
    if (target && stat(target, &expected) == 0 && fstat(fd, &actual) == 0 &&
        expected.st_dev == actual.st_dev && expected.st_ino == actual.st_ino) {
        errno = EIO;
        return -1;
    }
    return syscall(SYS_write, fd, buf, count);
}

/* This fixture forwards the one-argument prctl operations used by these
 * programs. Only the compiler child's parent-death setup is faulted. */
int prctl(int option, ...) {
    va_list args; va_start(args, option);
    unsigned long argument = va_arg(args, unsigned long);
    va_end(args);
    if (getenv("BUDGET_FAIL_PREEXEC") && option == PR_SET_PDEATHSIG && getpid() != initial_pid) {
        errno = EIO; return -1;
    }
    return syscall(SYS_prctl, option, argument, 0, 0, 0);
}
