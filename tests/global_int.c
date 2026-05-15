#include "local_assert.h"

int g;

void test(int x) {
    g = x;
    may_assert(g == x);
}
