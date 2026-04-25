#include "../local_assert.h"

int main(void) {
    int x = 2;
    int y = x + 3;
    may_assert(y == 5);
    return y;
}
