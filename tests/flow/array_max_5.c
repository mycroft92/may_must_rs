#include "../local_assert.h"

static int max_of_5(const int *values) {
    int current_max = values[0];
    for (int i = 1; i < 5; ++i) {
        if (values[i] > current_max) {
            current_max = values[i];
        }
    }
    return current_max;
}

int main(void) {
    int values[5] = {3, -7, 11, 4, 2};
    int computed_max = max_of_5(values);

    may_assert(computed_max >= values[0]);
    may_assert(computed_max >= values[1]);
    may_assert(computed_max >= values[2]);
    may_assert(computed_max >= values[3]);
    may_assert(computed_max >= values[4]);

    return computed_max;
}
