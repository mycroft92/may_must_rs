/*
 * verification.h — annotation header for the may-must assertion checker
 *
 * Usage:
 *   #include "verification.h"   (or compile with -include path/to/verification.h)
 *
 * Assertions — conditions that must hold on every reachable execution:
 *
 *   #include "verification.h"
 *   int abs(int x) {
 *       int result = x < 0 ? -x : x;
 *       assert(result >= 0);
 *       return result;
 *   }
 *
 * Assumptions — conditions that constrain the input space; paths where the
 * condition is false are treated as infeasible:
 *
 *   void bounded(int x) {
 *       assume(x >= 0 && x < 100);
 *       assert(x * x < 10000);
 *   }
 *
 * Both sentinels are removed from the visible CFG by the checker and have no
 * runtime effect, so they add zero overhead to production builds.
 *
 * To suppress the standard <assert.h> definition (if already included), define
 * NDEBUG before including this header, or include this header first.
 */

#ifndef VERIFICATION_H
#define VERIFICATION_H

/* Sentinel recognised by the checker as a verification obligation.
 * Stripped from the visible CFG; condition recorded as a backward WP seed. */
extern void may_assert(_Bool condition);

/* Sentinel recognised by the checker as a path feasibility constraint.
 * Stripped from the visible CFG; condition injected as TransferEffect::Assume
 * on the nearest CFG node, so WP weakens to (cond => post) at that point. */
extern void may_assume(_Bool condition);

/* Redefine assert() so existing code needs no source changes. */
#ifdef assert
#undef assert
#endif
#define assert(cond) may_assert((_Bool)(cond))

/* assume() is a fresh macro with no standard-library conflict. */
#define assume(cond) may_assume((_Bool)(cond))

#endif /* VERIFICATION_H */
