#include "../local_assert.h"

static int subject(int x, int y) {
    int positive = x > 0;
    int ordered = y >= x;
    may_assert(positive && ordered);
    return x + y;
}

int main(void) {
    return subject(1, 3);
}
