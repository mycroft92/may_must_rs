#include <stdio.h>

int main() {
    int sum = 0;
    int i, j, k;
    
    // Triple nested loop
    for (i = 0; i < 10; i++) {
        for (j = 0; j < 5; j++) {
            for (k = 0; k < 3; k++) {
                sum += i + j + k;
            }
        }
    }
    
    printf("Sum: %d\n", sum);
    
    // Nested while loops
    int x = 0;
    while (x < 3) {
        int y = 0;
        while (y < 4) {
            sum += x * y;
            y++;
        }
        x++;
    }
    
    printf("Final sum: %d\n", sum);
    
    return 0;
}
