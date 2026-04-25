#include "../local_assert.h"

__attribute__((noinline)) int inc(int x) {
    return x + 1;
}

__attribute__((noinline)) int dec(int x) {
    return x - 1;
}

static int subject(int x) {
    int y;
    if (x > 0) {
        y = inc(x);
    } else {
        y = dec(x);
    }
    may_assert(y != 0);
    return y;
}

int main(void) {
    return subject(4);
}
