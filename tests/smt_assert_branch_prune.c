#include "local_assert.h"

int main(int argc, char **argv) {
    (void)argv;

    int x = argc;

    if (x > 0) {
        may_assert(x > 0);
    } else {
        may_assert(1);
    }

    return 0;
}
