#include "local_assert.h"

int find_max3(int *arr) {
    int m = arr[0];
    if (arr[1] > m) m = arr[1];
    if (arr[2] > m) m = arr[2];
    return m;
}

int main() {
    int numbers[5] = {10, 20, 30, 40, 50};
    int m = find_max3(&numbers[2]);
    may_assert(m >= numbers[2]);
    may_assert(m >= numbers[3]);
    may_assert(m >= numbers[4]);
    return 0;
}
