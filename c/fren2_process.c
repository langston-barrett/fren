/* Process ownership primitives for Fren2's bounded solver transport and
   its test runner's deadline controller (`FrenOirToSmt.Process`). Lean's
   `IO.Process` spawns children and reads their pipes, but cannot observe
   a child's exit without reaping it (`waitid` with `WNOWAIT`), signal a
   process group, reap a group, catch termination signals, become a
   subreaper or hold a pidfd. These are those system calls and no more.

   Spawning is here too: a child that `IO.Process.spawn` returns keeps its
   pipes' handles alive once its `pid` is read (the stdin pipe then never
   closes), and its children inherit Lean's ignored SIGPIPE. These pipes are
   plain descriptors, which their Lean owner closes explicitly.

   A status is a `uint32_t`: `FREN2_RUNNING` while the child runs, the exit
   code (0-255) after a normal exit, or `0x100 | signal` after a fatal one. */

#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <spawn.h>
#include <stdlib.h>
#include <signal.h>
#include <stdint.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <lean/lean.h>
#ifdef __linux__
#include <sys/prctl.h>
#include <sys/syscall.h>
#endif

#define FREN2_RUNNING 0xFFFFFFFFu
#define FREN2_NO_CHILD 0xFFFFFFFFu

static lean_obj_res fren2_errno(const char *what) {
  int saved = errno;
  lean_object *name = lean_mk_string(what);
  lean_obj_res error = lean_decode_io_error(saved, name);
  lean_dec(name);
  return lean_io_result_mk_error(error);
}

static lean_obj_res fren2_ok_u32(uint32_t value) {
  return lean_io_result_mk_ok(lean_box_uint32(value));
}

static uint32_t fren2_encode(int status) {
  if (WIFEXITED(status)) return (uint32_t)WEXITSTATUS(status);
  if (WIFSIGNALED(status)) return 0x100u | (uint32_t)WTERMSIG(status);
  return FREN2_RUNNING;
}

extern char **environ;

/* Spawn `argv` (searched on PATH like `execvp`), in a new session when
   `session`, with SIGPIPE, SIGINT, SIGTERM and SIGHUP at their defaults and
   no signal blocked. With `pipes`, its stdin, stdout and stderr are new
   pipes, and the result is {pid, stdin, stdout, stderr} (the parent's ends,
   close-on-exec); otherwise it inherits them and the result is {pid}. */
LEAN_EXPORT lean_obj_res fren2_spawn(b_lean_obj_arg args, uint8_t session, uint8_t pipes,
                                     lean_obj_arg world) {
  (void)world;
  size_t n = lean_array_size(args);
  if (n == 0) {
    errno = EINVAL;
    return fren2_errno("spawn: empty command");
  }
  char **argv = calloc(n + 1, sizeof(char *));
  if (argv == NULL) return fren2_errno("spawn");
  for (size_t i = 0; i < n; i++) argv[i] = (char *)lean_string_cstr(lean_array_get_core(args, i));
  int fds[3][2] = {{-1, -1}, {-1, -1}, {-1, -1}};
  int error = 0;
  posix_spawn_file_actions_t actions;
  posix_spawnattr_t attr;
  posix_spawn_file_actions_init(&actions);
  posix_spawnattr_init(&attr);
  if (pipes) {
    for (int i = 0; i < 3 && error == 0; i++)
      if (pipe2(fds[i], O_CLOEXEC) != 0) error = errno;
    /* The child's end of each: stdin reads, stdout and stderr write. */
    for (int i = 0; i < 3 && error == 0; i++)
      error = posix_spawn_file_actions_adddup2(&actions, fds[i][i == 0 ? 0 : 1], i);
  }
  sigset_t defaults, none;
  sigemptyset(&defaults);
  sigaddset(&defaults, SIGPIPE);
  sigaddset(&defaults, SIGINT);
  sigaddset(&defaults, SIGTERM);
  sigaddset(&defaults, SIGHUP);
  sigemptyset(&none);
  short flags = POSIX_SPAWN_SETSIGDEF | POSIX_SPAWN_SETSIGMASK;
#ifdef POSIX_SPAWN_SETSID
  if (session) flags |= POSIX_SPAWN_SETSID;
#else
  if (session && error == 0) error = ENOSYS;
#endif
  if (error == 0) error = posix_spawnattr_setflags(&attr, flags);
  if (error == 0) error = posix_spawnattr_setsigdefault(&attr, &defaults);
  if (error == 0) error = posix_spawnattr_setsigmask(&attr, &none);
  pid_t pid = -1;
  if (error == 0) error = posix_spawnp(&pid, argv[0], &actions, &attr, argv, environ);
  posix_spawn_file_actions_destroy(&actions);
  posix_spawnattr_destroy(&attr);
  free(argv);
  for (int i = 0; i < 3; i++) {
    int child_end = fds[i][i == 0 ? 0 : 1], parent_end = fds[i][i == 0 ? 1 : 0];
    if (child_end >= 0) close(child_end);
    if (error != 0 && parent_end >= 0) close(parent_end);
  }
  if (error != 0) {
    errno = error;
    return fren2_errno("posix_spawn");
  }
  lean_object *result = lean_mk_empty_array();
  result = lean_array_push(result, lean_box_uint32((uint32_t)pid));
  if (pipes)
    for (int i = 0; i < 3; i++) result = lean_array_push(result, lean_box_uint32((uint32_t)fds[i][i == 0 ? 1 : 0]));
  return lean_io_result_mk_ok(result);
}

/* One read(2) of at most `max` bytes: what is available, or empty at EOF. */
LEAN_EXPORT lean_obj_res fren2_fd_read(uint32_t fd, size_t max, lean_obj_arg world) {
  (void)world;
  lean_object *buffer = lean_alloc_sarray(1, 0, max);
  for (;;) {
    ssize_t got = read((int)fd, lean_sarray_cptr(buffer), max);
    if (got >= 0) {
      lean_sarray_set_size(buffer, (size_t)got);
      return lean_io_result_mk_ok(buffer);
    }
    if (errno != EINTR) {
      lean_dec(buffer);
      return fren2_errno("read");
    }
  }
}

/* Write all of `bytes`; EPIPE (SIGPIPE is ignored) is an error. */
LEAN_EXPORT lean_obj_res fren2_fd_write(uint32_t fd, b_lean_obj_arg bytes, lean_obj_arg world) {
  (void)world;
  size_t size = lean_sarray_size(bytes), done = 0;
  const uint8_t *data = lean_sarray_cptr(bytes);
  while (done < size) {
    ssize_t put = write((int)fd, data + done, size - done);
    if (put >= 0) done += (size_t)put;
    else if (errno != EINTR) return fren2_errno("write");
  }
  return lean_io_result_mk_ok(lean_box(0));
}

/* Observe without reaping: the unreaped leader keeps its PID, and so the
   numeric process group, from being reused. ECHILD is an error: ownership
   was lost, and the caller must not signal that group. */
LEAN_EXPORT lean_obj_res fren2_observe_exit(uint32_t pid, lean_obj_arg world) {
  (void)world;
  siginfo_t info;
  for (;;) {
    memset(&info, 0, sizeof info);
    if (waitid(P_PID, (id_t)pid, &info, WEXITED | WNOHANG | WNOWAIT) == 0) break;
    if (errno != EINTR) return fren2_errno("waitid");
  }
  if (info.si_pid == 0) return fren2_ok_u32(FREN2_RUNNING);
  if (info.si_code == CLD_EXITED) return fren2_ok_u32((uint32_t)info.si_status & 0xFFu);
  return fren2_ok_u32(0x100u | ((uint32_t)info.si_status & 0xFFu));
}

/* Signal a process group (0: the caller's own). False if it is gone. */
LEAN_EXPORT lean_obj_res fren2_signal_group(uint32_t pgid, uint32_t sig, lean_obj_arg world) {
  (void)world;
  if (killpg((pid_t)pgid, (int)sig) == 0) return lean_io_result_mk_ok(lean_box(1));
  if (errno == ESRCH) return lean_io_result_mk_ok(lean_box(0));
  return fren2_errno("killpg");
}

/* Signal one process by PID (only the caller's own PID or an unreaped
   child of the caller, whose PID cannot have been reused). */
LEAN_EXPORT lean_obj_res fren2_signal_process(uint32_t pid, uint32_t sig, lean_obj_arg world) {
  (void)world;
  if (kill((pid_t)pid, (int)sig) == 0) return lean_io_result_mk_ok(lean_box(1));
  if (errno == ESRCH) return lean_io_result_mk_ok(lean_box(0));
  return fren2_errno("kill");
}

/* Signal the calling thread (`raise`): unlike `kill` of the process, the
   signal is handled before this returns, whichever thread runs Lean's
   `main`, unless it is blocked. */
LEAN_EXPORT lean_obj_res fren2_raise(uint32_t sig, lean_obj_arg world) {
  (void)world;
  if (raise((int)sig) == 0) return lean_io_result_mk_ok(lean_box(0));
  return fren2_errno("raise");
}

/* Reap one child, blocking: its status. */
LEAN_EXPORT lean_obj_res fren2_reap(uint32_t pid, lean_obj_arg world) {
  (void)world;
  int status = 0;
  while (waitpid((pid_t)pid, &status, 0) < 0)
    if (errno != EINTR) return fren2_errno("waitpid");
  return fren2_ok_u32(fren2_encode(status));
}

/* Reap one member of a process group: its PID, 0 if none has exited yet
   (only when not blocking), or FREN2_NO_CHILD when none is left. */
LEAN_EXPORT lean_obj_res fren2_reap_group(uint32_t pgid, uint8_t block, lean_obj_arg world) {
  (void)world;
  int status = 0;
  for (;;) {
    pid_t pid = waitpid(-(pid_t)pgid, &status, block ? 0 : WNOHANG);
    if (pid >= 0) return fren2_ok_u32((uint32_t)pid);
    if (errno == ECHILD) return fren2_ok_u32(FREN2_NO_CHILD);
    if (errno != EINTR) return fren2_errno("waitpid");
  }
}

LEAN_EXPORT lean_obj_res fren2_parent_pid(lean_obj_arg world) {
  (void)world;
  return fren2_ok_u32((uint32_t)getppid());
}

/* Orphaned descendants of the controller's job are adopted by it. */
LEAN_EXPORT lean_obj_res fren2_set_subreaper(lean_obj_arg world) {
  (void)world;
#ifdef __linux__
  if (prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) == 0) return lean_io_result_mk_ok(lean_box(0));
  return fren2_errno("prctl(PR_SET_CHILD_SUBREAPER)");
#else
  errno = ENOSYS;
  return fren2_errno("subreaper");
#endif
}

LEAN_EXPORT lean_obj_res fren2_close_fd(uint32_t fd, lean_obj_arg world) {
  (void)world;
  if (close((int)fd) == 0) return lean_io_result_mk_ok(lean_box(0));
  return fren2_errno("close");
}

/* A pidfd names one process for good: after it is reaped, signals through
   the pidfd fail with ESRCH even if its numeric PID is reused. */
LEAN_EXPORT lean_obj_res fren2_pidfd_open(uint32_t pid, lean_obj_arg world) {
  (void)world;
#if defined(__linux__) && defined(SYS_pidfd_open)
  long fd = syscall(SYS_pidfd_open, (pid_t)pid, 0);
  if (fd >= 0) return fren2_ok_u32((uint32_t)fd);
  return fren2_errno("pidfd_open");
#else
  errno = ENOSYS;
  return fren2_errno("pidfd_open");
#endif
}

LEAN_EXPORT lean_obj_res fren2_pidfd_signal(uint32_t fd, uint32_t sig, lean_obj_arg world) {
  (void)world;
#if defined(__linux__) && defined(SYS_pidfd_send_signal)
  if (syscall(SYS_pidfd_send_signal, (int)fd, (int)sig, NULL, 0) == 0)
    return lean_io_result_mk_ok(lean_box(1));
  if (errno == ESRCH) return lean_io_result_mk_ok(lean_box(0));
  return fren2_errno("pidfd_send_signal");
#else
  errno = ENOSYS;
  return fren2_errno("pidfd_send_signal");
#endif
}

/* Cancellation by SIGINT, SIGTERM or SIGHUP. While at least one watch is
   open, a handler records the first such signal and does nothing else, so
   it cannot interrupt the owner's kill and reap. When the last watch
   closes, the previous dispositions return; if a signal was recorded and
   the closer asks, it is raised again, now under the previous disposition,
   so the process ends (or not) as it would have without the watch. */
static const int fren2_cancel_signals[3] = {SIGINT, SIGTERM, SIGHUP};
static struct sigaction fren2_previous[3];
static volatile sig_atomic_t fren2_first_signal = 0;
static unsigned fren2_watchers = 0;
static pthread_mutex_t fren2_watch_lock = PTHREAD_MUTEX_INITIALIZER;

static void fren2_record_signal(int sig) {
  int expected = 0;
  __atomic_compare_exchange_n((int *)&fren2_first_signal, &expected, sig, 0,
                              __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
}

LEAN_EXPORT lean_obj_res fren2_watch_begin(lean_obj_arg world) {
  (void)world;
  pthread_mutex_lock(&fren2_watch_lock);
  if (fren2_watchers == 0) {
    struct sigaction action;
    memset(&action, 0, sizeof action);
    action.sa_handler = fren2_record_signal;
    sigemptyset(&action.sa_mask);
    action.sa_flags = SA_RESTART;
    for (int i = 0; i < 3; i++) {
      if (sigaction(fren2_cancel_signals[i], &action, &fren2_previous[i]) != 0) {
        int saved = errno;
        for (int j = 0; j < i; j++) sigaction(fren2_cancel_signals[j], &fren2_previous[j], NULL);
        pthread_mutex_unlock(&fren2_watch_lock);
        errno = saved;
        return fren2_errno("sigaction");
      }
    }
  }
  fren2_watchers++;
  pthread_mutex_unlock(&fren2_watch_lock);
  return lean_io_result_mk_ok(lean_box(0));
}

/* The first recorded signal, or 0. */
LEAN_EXPORT lean_obj_res fren2_watched_signal(lean_obj_arg world) {
  (void)world;
  return fren2_ok_u32((uint32_t)__atomic_load_n((int *)&fren2_first_signal, __ATOMIC_SEQ_CST));
}

/* Close one watch: the recorded signal, or 0. The last watch restores the
   previous dispositions, clears the record and, with `reraise`, raises the
   recorded signal again. */
LEAN_EXPORT lean_obj_res fren2_watch_end(uint8_t reraise, lean_obj_arg world) {
  (void)world;
  pthread_mutex_lock(&fren2_watch_lock);
  int sig = __atomic_load_n((int *)&fren2_first_signal, __ATOMIC_SEQ_CST);
  if (fren2_watchers > 0 && --fren2_watchers == 0) {
    for (int i = 0; i < 3; i++) sigaction(fren2_cancel_signals[i], &fren2_previous[i], NULL);
    /* A signal that arrives between the restore and this clear was taken
       by the previous disposition already; this record is older. */
    sig = __atomic_exchange_n((int *)&fren2_first_signal, 0, __ATOMIC_SEQ_CST);
    pthread_mutex_unlock(&fren2_watch_lock);
    if (reraise && sig != 0) {
      sigset_t one;
      sigemptyset(&one);
      sigaddset(&one, sig);
      pthread_sigmask(SIG_UNBLOCK, &one, NULL);
      raise(sig);
    }
    return fren2_ok_u32((uint32_t)sig);
  }
  pthread_mutex_unlock(&fren2_watch_lock);
  return fren2_ok_u32((uint32_t)sig);
}
