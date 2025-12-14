#include <stdio.h>
#include <stdlib.h>

void fibonacci(int n, int *result) {
    if (n <= 1) {
        *result = n;
        return;
    }
    
    int prev1, prev2;
    fibonacci(n - 1, &prev1);
    fibonacci(n - 2, &prev2);
    *result = prev1 + prev2;
}

// Iterative version using pointers
void fibonacci_iterative(int n, int *result) {
    if (n <= 1) {
        *result = n;
        return;
    }
    
    int *a = malloc(sizeof(int));
    int *b = malloc(sizeof(int));
    *a = 0;
    *b = 1;
    
    for (int i = 2; i <= n; i++) {
        int temp = *a + *b;
        *a = *b;
        *b = temp;
    }
    
    *result = *b;
    free(a);
    free(b);
}

int main() {
    int n = 10;
    int fib_result;
    
    printf("Fibonacci numbers (recursive with pointers):\n");
    for (int i = 0; i <= n; i++) {
        fibonacci(i, &fib_result);
        printf("F(%d) = %d\n", i, fib_result);
    }
    
    printf("\nFibonacci of %d (iterative): ", n);
    fibonacci_iterative(n, &fib_result);
    printf("%d\n", fib_result);
    
    return 0;
}
