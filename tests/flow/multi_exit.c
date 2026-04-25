#include "../local_assert.h"

static int subject(int x) {
    if (x < 0) {
        may_assert(1);
        return -1;
    }
    may_assert(x >= 0);
    return x;
}

int main(void) {
    return subject(2);
}
