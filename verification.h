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

/* ---------------------------------------------------------------------------
 * Bounded nondeterministic values
 *
 * Each nondet_*() macro calls an opaque external source and then uses
 * assume() to constrain the result to the C type's range.  This keeps the
 * SMT model sound: the checker's integer model is unbounded, so without these
 * constraints an "unsigned int" could take the value -1 and produce a false
 * counterexample.
 *
 * The macros use GCC/Clang statement expressions ({ ... }), which expand
 * inline at the call site and are unaffected by -fno-inline.
 *
 * Usage:
 *   unsigned int n = nondet_uint();   // guaranteed >= 0 in the SMT model
 *   char c         = nondet_char();   // guaranteed in [-128, 127]
 * -------------------------------------------------------------------------*/

/* Opaque source of nondeterminism — an unconstrained external integer.
 * Do not call directly; use the typed nondet_*() macros below. */
extern int __may_nondet_raw(void);

/* Signed types — the SMT integer model already matches; no bound needed. */
#define nondet_int()  (__may_nondet_raw())
#define nondet_long() (__may_nondet_raw())

/* Unsigned types — lower-bound only for 32-bit/64-bit (upper bound
 * 2^32−1 or 2^64−1 doesn't fit in a signed SMT integer without care;
 * non-negativity is the critical constraint for soundness). */
#define nondet_uint() \
    __extension__({ int _v = __may_nondet_raw(); assume(_v >= 0); _v; })
#define nondet_ulong() \
    __extension__({ int _v = __may_nondet_raw(); assume(_v >= 0); _v; })

/* Small unsigned types — full range constraints since they fit in i64. */
#define nondet_uchar() \
    __extension__({ int _v = __may_nondet_raw(); assume(_v >= 0); assume(_v <= 255); _v; })
#define nondet_ushort() \
    __extension__({ int _v = __may_nondet_raw(); assume(_v >= 0); assume(_v <= 65535); _v; })

/* Small signed types — full range constraints. */
#define nondet_char() \
    __extension__({ int _v = __may_nondet_raw(); assume(_v >= -128); assume(_v <= 127); _v; })
#define nondet_short() \
    __extension__({ int _v = __may_nondet_raw(); assume(_v >= -32768); assume(_v <= 32767); _v; })

/* Boolean — constrained to {0, 1}. */
#define nondet_bool() \
    __extension__({ int _v = __may_nondet_raw(); assume(_v == 0 || _v == 1); _v; })

#endif /* VERIFICATION_H */
