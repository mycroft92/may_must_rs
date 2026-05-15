/*
 * verification.h — annotation header for the may-must assertion checker
 *
 * Usage:
 *   #include "verification.h"   (or compile with -include path/to/verification.h)
 *
 * Write assertions using the standard assert() macro:
 *
 *   #include "verification.h"
 *   int abs(int x) {
 *       int result = x < 0 ? -x : x;
 *       assert(result >= 0);
 *       return result;
 *   }
 *
 * The checker removes may_assert() calls from the visible CFG and records the
 * condition as a formal verification obligation.  At runtime (outside the
 * checker) may_assert() is a no-op, so assertions add no overhead to
 * production builds.
 *
 * To suppress the standard <assert.h> definition (if already included), define
 * NDEBUG before including this header, or include this header first.
 */

#ifndef VERIFICATION_H
#define VERIFICATION_H

/* Sentinel function recognised and stripped by the checker. */
extern void may_assert(_Bool condition);

/* Redefine assert() so existing code needs no source changes.
 * Defining assert as a macro here shadows any definition from <assert.h>. */
#ifdef assert
#undef assert
#endif
#define assert(cond) may_assert((_Bool)(cond))

#endif /* VERIFICATION_H */
