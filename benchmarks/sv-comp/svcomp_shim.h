/*
 * svcomp_shim.h — bridges SV-COMP verification sentinels to our intrinsics.
 *
 * Include this AFTER removing extern declarations of __VERIFIER_error from
 * the source (convert.py does this automatically).  Compile with -include or
 * prepend via convert.py; do not include it manually inside source files you
 * plan to check independently.
 *
 * Sentinel mapping
 * ----------------
 *  __VERIFIER_error()      → may_assert(0)   (assert false at this point)
 *  __VERIFIER_assume(cond) → assume(cond)     (constrain the input space)
 *  __VERIFIER_nondet_*()   → nondet_*() macros (bounded nondeterministic
 *                                               inputs from verification.h;
 *                                               unsigned types get assume >= 0)
 */

#ifndef SVCOMP_SHIM_H
#define SVCOMP_SHIM_H

#include "../../verification.h"

/* Reachability property: __VERIFIER_error() must never be called.
 * We lower each call site to may_assert(0), so the checker must prove
 * that control never reaches this point. */
#define __VERIFIER_error() may_assert((_Bool)0)

/* Many benchmarks use __VERIFIER_assert(cond) instead of (or in addition to)
 * __VERIFIER_error().  It is typically defined as a function that calls
 * reach_error() / __VERIFIER_error() when cond is false.  We replace every
 * call site with may_assert so the checker sees it as a verification
 * obligation.  convert.py strips the function definition to avoid conflicts. */
#define __VERIFIER_assert(cond) may_assert((_Bool)(cond))

/* reach_error() is a helper called by __VERIFIER_assert; with the function
 * definition stripped by convert.py the macro replacement here is a no-op
 * (the call sites disappear through __VERIFIER_assert expansion). */
#define reach_error() may_assert((_Bool)0)

/* Path feasibility: assume(cond) prunes paths where cond is false. */
#define __VERIFIER_assume(cond) assume((_Bool)(cond))

/* Nondeterministic inputs — mapped to our bounded nondet_*() macros from
 * verification.h.  Unsigned and small-range types get assume() constraints
 * so the SMT model stays sound (unbounded integers would allow -1 for
 * "unsigned int", producing false counterexamples).
 *
 * Floating-point nondet is left as an extern stub; the checker reports
 * UNKNOWN for programs that use float/double. */
#define __VERIFIER_nondet_int()    nondet_int()
#define __VERIFIER_nondet_uint()   nondet_uint()
#define __VERIFIER_nondet_long()   nondet_long()
#define __VERIFIER_nondet_ulong()  nondet_ulong()
#define __VERIFIER_nondet_short()  nondet_short()
#define __VERIFIER_nondet_ushort() nondet_ushort()
#define __VERIFIER_nondet_char()   nondet_char()
#define __VERIFIER_nondet_uchar()  nondet_uchar()
#define __VERIFIER_nondet_bool()   nondet_bool()
extern float             __VERIFIER_nondet_float(void);
extern double            __VERIFIER_nondet_double(void);

#endif /* SVCOMP_SHIM_H */
