#include <stdio.h>
#include <assert.h>

int main() {
    int sum = 0;
    int n = 5;
    
    // Loop to calculate sum of numbers 1 to n
    for (int i = 1; i <= n; i++) {
        sum += i;
    }
    
    // Assert that the sum equals the expected formula: n*(n+1)/2
    assert(sum == n * (n + 1) / 2);
    
    printf("Sum of 1 to %d is %d\n", n, sum);
    printf("Assertion passed!\n");
    
    return 0;
}
