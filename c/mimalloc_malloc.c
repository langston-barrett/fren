/* The binary's `malloc`, and the functions around it, on Linux with glibc:
   mimalloc's, which Lean's runtime already links into every executable for
   Lean's own objects (`mi_*`). cvc5 allocates and frees through `malloc`,
   its terms directly and the rest through libc++'s `operator new`, and
   glibc's allocator took about a sixth of the solver's cycles; with
   mimalloc, the solver runs Fren's own spec's queries in about 19% fewer
   cycles, with the same answers (#549, round 7).

   A definition of `malloc` in the executable takes the place of glibc's
   for the whole process, glibc's own calls to it included, since the
   dynamic linker resolves every library's `malloc` to the executable's.
   So every block is allocated and freed by mimalloc, and none crosses
   from one allocator to the other. Every function that glibc's manual
   lists for replacing `malloc` ("Replacing malloc") is here, with
   `reallocarray`, `cfree`, and glibc's internal names for them, so that
   none is left to glibc's allocator.

   The executables that run the Lean-hosted front end, whose solvers are
   never freed, also have mimalloc commit memory only as it needs it
   (`c/mimalloc_lazy_commit.c`).

   The `mi_*` functions are those of Lean's runtime, so a toolchain without
   them fails to link rather than run with two allocators.

   Elsewhere this file defines nothing: on macOS, a system library's own
   allocations would stay the system's, and could then reach mimalloc's
   `free`. */

#include <stdint.h>
#ifdef __linux__
#include <lean/mimalloc.h>
#include <stdlib.h>
#include <string.h>
#endif

#ifdef __GLIBC__

void *malloc(size_t size) { return mi_malloc(size); }
void *calloc(size_t count, size_t size) { return mi_calloc(count, size); }
void *realloc(void *p, size_t newsize) { return mi_realloc(p, newsize); }
void free(void *p) { mi_free(p); }
void cfree(void *p) { mi_cfree(p); }
void *reallocarray(void *p, size_t count, size_t size) { return mi_reallocarray(p, count, size); }
void *memalign(size_t alignment, size_t size) { return mi_memalign(alignment, size); }
int posix_memalign(void **p, size_t alignment, size_t size) { return mi_posix_memalign(p, alignment, size); }
void *aligned_alloc(size_t alignment, size_t size) { return mi_aligned_alloc(alignment, size); }
void *valloc(size_t size) { return mi_valloc(size); }
void *pvalloc(size_t size) { return mi_pvalloc(size); }
size_t malloc_usable_size(void *p) { return mi_usable_size(p); }

/* glibc's internal names, which some libraries call directly. */
void *__libc_malloc(size_t size) { return mi_malloc(size); }
void *__libc_calloc(size_t count, size_t size) { return mi_calloc(count, size); }
void *__libc_realloc(void *p, size_t newsize) { return mi_realloc(p, newsize); }
void __libc_free(void *p) { mi_free(p); }
void *__libc_memalign(size_t alignment, size_t size) { return mi_memalign(alignment, size); }
void *__libc_valloc(size_t size) { return mi_valloc(size); }
void *__libc_pvalloc(size_t size) { return mi_pvalloc(size); }
int __posix_memalign(void **p, size_t alignment, size_t size) { return mi_posix_memalign(p, alignment, size); }

/* Whether a block that glibc allocates for itself, by `strdup`, is
   mimalloc's: 1 if it is, 0 if not. For `fren_test`'s `solverLifetime`
   job, as `mallocIsMimalloc` in `src/FrenTestMain.lean`; the argument is
   Lean's unit. */
uint32_t fren_malloc_is_mimalloc(void *unit) {
  (void)unit;
  char *p = strdup("fren");
  uint32_t owned = p != NULL && mi_is_in_heap_region(p);
  free(p);
  return owned;
}

#else

/* 2: this file replaces no allocator here. */
uint32_t fren_malloc_is_mimalloc(void *unit) {
  (void)unit;
  return 2;
}

#endif
