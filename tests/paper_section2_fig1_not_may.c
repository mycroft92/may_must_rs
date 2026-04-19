#include "local_assert.h"

/*
 * Target example from SMASH Section 2, Figure 1.
 *
 * This should eventually be proved SAFE by computing/reusing the not-may
 * summary:
 *
 *   <true not-may=> g (retval < 0)>
 *
 * It is kept as a target fixture for direct-call summary composition. The
 * paper writes this as main(int i1, int i2, int i3), but C only gives main a
 * few portable signatures, so the target procedure is named explicitly here.
 * The current --engine smt path is intraprocedural, so this file is built by
 * the IR target but not yet part of smt-smoke.
 */

int g(int i) {
    if (i > 0) {
        return i;
    }

    return -i;
}

int section2_example1_not_may(int i1, int i2, int i3) {
    int x1 = g(i1);
    int x2 = g(i2);
    int x3 = g(i3);

    if ((x1 < 0) || (x2 < 0) || (x3 < 0)) {
        may_assert(0);
    }

    return 0;
}
