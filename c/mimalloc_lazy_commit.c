/* For the executables that run the Lean-hosted front end (`fren_test`,
   `fren_fuzz_frontends`, `fren_coverage`): mimalloc commits the memory of
   each arena that it reserves as it needs it, rather than all at once.

   lean-smt never frees its solvers (#549), and once `c/mimalloc_malloc.c`
   gives cvc5's allocations to mimalloc, those solvers took a third more
   resident memory with arenas committed at once: 5.9-6.2 GB, against
   4.2 GB with glibc's allocator, for `fren_test --job frontendFuzz 0 30`.
   Committed as needed, they take 4.2 GB again. The `fren` binary keeps
   mimalloc's default, which costs it no memory and about 1% fewer cycles.

   Set by a constructor of priority 101, which runs before the
   executable's other constructors and `main`, and so before cvc5's and
   Lean's allocations. The shared libraries' constructors and the dynamic
   linker run earlier and may allocate with mimalloc first, so mimalloc may
   already have reserved an arena under eager commit; the setting applies
   to the arenas that it reserves after it. */

#ifdef __linux__
#include <lean/mimalloc.h>
#include <stdlib.h>
#endif

#ifdef __GLIBC__

__attribute__((constructor(101))) static void fren_mimalloc_lazy_commit(void) {
  mi_option_set(mi_option_arena_eager_commit, 0);
}

#else

/* A translation unit must declare something. */
typedef int fren_mimalloc_lazy_commit_unused;

#endif
