#include "local_assert.h"

int main() {
    int nums[3] = {7, 8, 9};
    may_assert(nums[0] == 7);
    may_assert(nums[1] == 8);
    may_assert(nums[2] == 9);
    return 0;
}
