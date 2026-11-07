/* Only fren_test's explicitly protected child processes use this hook.
   RLIMIT_CORE=0 alone does not stop Linux's piped core collectors, which
   can delay reaping after a fatal signal. Set dumpability after exec,
   before the runtime starts, without changing any signal disposition. */

#include <stdio.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <unistd.h>
#include <lean/lean.h>
#ifdef __linux__
#include <sys/prctl.h>
#endif

/* Raise on the checking worker itself, without a signal helper process
   or pipe-reader threads at the controlled fatal stop. */
LEAN_EXPORT lean_obj_res fren_test_raise_abrt(lean_obj_arg world) {
  (void)world;
  raise(SIGABRT);
  return lean_io_result_mk_error(lean_mk_io_user_error(
    lean_mk_string("native ABRT probe returned from raise")));
}

__attribute__((constructor)) static void fren_native_test_core(void) {
  const char *enabled = getenv("FREN_NATIVE_CORELESS");
  if (enabled == NULL || strcmp(enabled, "1") != 0) return;
  struct rlimit limit = {0, 0};
  if (setrlimit(RLIMIT_CORE, &limit) != 0) goto failed;
#ifdef __linux__
  if (prctl(PR_SET_DUMPABLE, 0, 0, 0, 0) != 0 ||
      prctl(PR_GET_DUMPABLE, 0, 0, 0, 0) != 0) goto failed;
#endif
  const char *path = getenv("FREN_ENUM_PROGRESS");
  if (path == NULL) path = getenv("FREN_OWN_SPEC_PROGRESS");
  if (path != NULL) {
    FILE *journal = fopen(path, "a");
    if (journal == NULL) goto failed;
#ifdef __linux__
    int written = fputs("[\"native-core-policy\",\"rlimit=0\",\"dumpable=0\"]\n", journal);
#else
    int written = fputs("[\"native-core-policy\",\"rlimit=0\",\"rlimit-only\"]\n", journal);
#endif
    int closed = fclose(journal);
    if (written < 0 || closed != 0) goto failed;
  }
  return;
failed:
  fputs("native test core protection failed\n", stderr);
  _exit(125);
}
