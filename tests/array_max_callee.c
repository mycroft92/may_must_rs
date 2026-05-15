#include "local_assert.h"

int find_max(int *arr) {
    int max = arr[0];
    if (arr[1] > max) max = arr[1];
    if (arr[2] > max) max = arr[2];
    if (arr[3] > max) max = arr[3];
    if (arr[4] > max) max = arr[4];
    return max;
}

int main() {
    int numbers[5] = {10, 20, 30, 40, 50};
    int m = find_max(numbers);
    may_assert(m >= numbers[0]);
    may_assert(m >= numbers[1]);
    may_assert(m >= numbers[2]);
    may_assert(m >= numbers[3]);
    may_assert(m >= numbers[4]);
    return 0;
}
