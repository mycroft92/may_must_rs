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
 *  __VERIFIER_nondet_*()   → extern stubs     (unconstrained inputs — the
 *                                               checker models unknown calls
 *                                               as producing arbitrary values)
 */

#ifndef SVCOMP_SHIM_H
#define SVCOMP_SHIM_H

#include "../../verification.h"

/* Reachability property: __VERIFIER_error() must never be called.
 * We lower each call site to may_assert(0), so the checker must prove
 * that control never reaches this point. */
#define __VERIFIER_error() may_assert((_Bool)0)

/* Path feasibility: assume(cond) prunes paths where cond is false. */
#define __VERIFIER_assume(cond) assume((_Bool)(cond))

/* Nondeterministic inputs — declared so source files compile cleanly.
 * The checker treats these as unconstrained external calls, which is
 * semantically correct for a sound over-approximation. */
extern int               __VERIFIER_nondet_int(void);
extern unsigned int      __VERIFIER_nondet_uint(void);
extern long              __VERIFIER_nondet_long(void);
extern unsigned long     __VERIFIER_nondet_ulong(void);
extern short             __VERIFIER_nondet_short(void);
extern unsigned short    __VERIFIER_nondet_ushort(void);
extern char              __VERIFIER_nondet_char(void);
extern unsigned char     __VERIFIER_nondet_uchar(void);
extern _Bool             __VERIFIER_nondet_bool(void);
extern float             __VERIFIER_nondet_float(void);
extern double            __VERIFIER_nondet_double(void);

#endif /* SVCOMP_SHIM_H */
