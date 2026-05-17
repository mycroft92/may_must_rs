#include "../../verification.h"

// Two distinct stack allocas must have different flat addresses.
// ptrtoint produces distinct concrete integers; the assertion is safe.
void test_distinct_stack_addrs(void) {
    int a = 1;
    int b = 2;
    unsigned int addr_a = (unsigned int)&a;
    unsigned int addr_b = (unsigned int)&b;
    may_assert(addr_a != addr_b);
}
