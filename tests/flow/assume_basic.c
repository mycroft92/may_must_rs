/*
 * assume_basic.c — smoke test for assume(cond) path-feasibility constraints.
 *
 * Each assertion below is discharged by a preceding assume.  All three should
 * be reported SAFE by the checker.
 */
#include "../local_assert.h"

/* assume(x > 0) makes assert(x > 0) trivially true. */
int same_condition(int x) {
    assume(x > 0);
    assert(x > 0);
    return x;
}

/* assume(x > 0) implies x >= 0, so the weaker assertion is also discharged. */
int weaker_assertion(int x) {
    assume(x > 0);
    assert(x >= 0);
    return x;
}

/* Bounded input: assume x in [1,9], assert x*x < 100. */
int bounded_square(int x) {
    assume(x >= 1);
    assume(x <= 9);
    assert(x * x < 100);
    return x * x;
}

int main(void) {
    same_condition(5);
    weaker_assertion(3);
    bounded_square(7);
    return 0;
}
