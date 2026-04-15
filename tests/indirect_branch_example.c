#include <stdio.h>

int indirect_branch_example(int selector) {
    static void *targets[] = {&&block1, &&block2, &&block3};

    if (selector < 0 || selector > 2) {
        return -1;
    }

    goto *targets[selector];

block1:
    return 1;
block2:
    return 2;
block3:
    return 3;
}

int main(void) {
    for (int i = 0; i < 3; i++) {
        printf("Result value: %d\n", indirect_branch_example(i));
    }

    return 0;
}
