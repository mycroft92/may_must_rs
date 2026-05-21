#include "local_assert.h"

/* Compact search pattern with a small array.
 *
 * Fill array[N] with nondet chars, then search for a nondet target ND.
 * If no element matches, the assert(0) fires — always reachable.
 *
 * The small array size (N=3) lets DART enumerate all paths in a few
 * iterations so the UNSAFE verdict is found via forward concrete exploration.
 *
 * Regression for the vacuous-initiation soundness bug (v0.20.0): when
 * forward_reach_at_header returned False for the search loop (sequential
 * counting loop pattern), any invariant candidate passed initiation trivially,
 * producing a spurious SAFE verdict on the full-size benchmark compact.c.
 */

#define N 3

int main(void) {
    char array[N];
    char ND = nondet_char();
    unsigned int i;

    for (i = 0; i < N; i++)
        array[i] = nondet_char();

    for (i = 0; i < N; i++)
        if (array[i] == ND)
            return (int)i;

    assert(0);
    return 0;
}
