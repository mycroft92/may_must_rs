#include "../local_assert.h"

static int subject(int n) {
    int i = 0;
    while (i < n) {
        i = i + 1;
    }
    may_assert(i >= 0);
    return i;
}

int main(void) {
    return subject(4);
}
