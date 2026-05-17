// Verify that two malloc call sites produce distinct abstract regions so that
// writes through one pointer do not alias writes through the other.
#include "local_assert.h"
#include <stdlib.h>

void heap_distinct(void) {
    int *a = (int *)malloc(sizeof(int));
    int *b = (int *)malloc(sizeof(int));
    *a = 1;
    *b = 2;
    // If both pointers shared one abstract region the store to *b would
    // overwrite the constraint on *a and the assertion could fail.
    may_assert(*a == 1);
}
