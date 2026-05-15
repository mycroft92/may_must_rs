#include "local_assert.h"

/* Basic struct field read/write verification.
 * Each assertion checks that a previously stored field value is correct.
 * With per-field memory regions (Step 2), the solver needs no array-theory
 * reasoning to discharge these: each field lives in its own scalar region. */
struct Point {
    int x;
    int y;
};

int main() {
    struct Point p;
    p.x = 3;
    p.y = 7;
    may_assert(p.x == 3);
    may_assert(p.y == 7);
    /* Cross-field: x did not change when y was written */
    may_assert(p.x + p.y == 10);
    return 0;
}
