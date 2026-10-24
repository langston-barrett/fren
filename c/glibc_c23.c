/* glibc 2.38 and later name C23's `strtol` and `fscanf` `__isoc23_strtol`
   and `__isoc23_fscanf`. cvc5's static Linux release calls those, but Lean
   links executables against an older glibc that lacks them, so they are
   defined here by the functions they replace. C23's only difference, the
   `0b` prefix, doesn't arise in cvc5's uses (option parsing, and reading
   `/proc`). This file must not be compiled as C23, where `strtol` itself
   becomes `__isoc23_strtol`; the build passes `-std=gnu17`. */

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

long __isoc23_strtol(const char *s, char **end, int base) { return strtol(s, end, base); }

int __isoc23_fscanf(FILE *f, const char *format, ...) {
  va_list args;
  va_start(args, format);
  int n = vfscanf(f, format, args);
  va_end(args);
  return n;
}
